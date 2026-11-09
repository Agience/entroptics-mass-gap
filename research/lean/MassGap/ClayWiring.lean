import Mathlib
import MassGap.ClayStatement
import MassGap.ClayTiltedFull
import MassGap.ApertureFinal
import MassGap.LocalLink

/-!
# MassGap.ClayWiring — the rooted results wired into `ClayStatement.ClayStatementAt`

`ClayStatement.clayStatementAt_of_link` takes twenty-one inputs and the composite data `C`, `wC`. This module discharges the ones the
rooted results already give and restates the rest on the objects they read, so that each remaining
input is a new obligation.

## The mixing of a per-field factor

The local route (`ApertureVolume.clay_two`, `ApertureFinal.diagBoundSep_zOwn_of_nearOwn`) works with a
per-field factor `Z k O` (`Renorm.connected Z`, at `Z = zOwn`). `ClayStatement` works with a mixing
`RenormMix`. `mixOfZ B op m Z` is the mixing with basis `op : B → LField`, step-independent
coefficients `m α b` and the step dependence carried by the per-field factor:
`M k α b = m α b · Z k (op b)`. Then (`latT_mixOfZ`)

  `latT k F = ∑_b ∏ᵢ coefC m cᵢ bᵢ · latSkR (connected Z) k ((op bᵢ, fᵢ))ᵢ`,

a finite combination, with constant coefficients `coefC m c b = ∑_α c_α m α b`, of the local route's
own readings. Each irreducible `O(4)` channel then renormalises with the factor of the basis fields
that carry it.

## What is discharged

* **SepConv** (`sepConv_mixOfZ`): from `DiagBoundSep` at `Z` alone. E on the reflection diagonal
  bounds every separated family (`ClayTiltedFull.exists_abs_latSkR_le_of_diagBoundClass`, at the class
  of all test functions), so each reading converges along `ultra`, and so does the finite combination.
  The value is `contT_mixOfZ`.
* **OS1 at dyadic translations** (`contT_translate_dyadic`): `contT` is unchanged by every translation
  `site a_j p`, from the lattice translation invariance of the Wilson state
  (`ClayTiltedFull.latSkRAlong_translate`), with no hypothesis.
* **OS1Sep** (`os1Sep_mixOfZ`): from `SepConv` and continuity of `v ↦ contT (F + v)` (`TransContT`);
  the dyadic vectors approximate every `v` (`tendsto_dyadic_approx`).
* **OS0** (`abs_contT_mixOfZ_le`): every bound `T` on the basis readings of an admissible family
  gives `|S(F)| ≤ (|B| · ∑|m|)ⁿ ∏ ‖cᵢ‖₁ · T`, whatever the form of `T`. `os0Sep_mixOfZ` is it at the
  kernel form `α γⁿ (n!)^β d^{−κn} ∏ ‖cᵢ‖₁ ‖fᵢ‖_{L¹}` of `OS0Sep`, from the same form on the basis
  readings (`OS0Own`), with the same `β, κ`.
* **The Riemann symmetries** (`riemann_mixOfZ`) from those of `m` (`CoefRiemann`).
* **ScalarTie** (`scalarTie_mixOfZ`): when the trace coefficient vector is `κ` on one basis field
  `op b0 = sym (plaqField q0)` and `0` on the others, the tie is `κ Z_k(op b0) a_k⁴ → N/8`.
* **The convergence half of LinkTS** (`linkTS_of_hs`): `ΘP ∪ Q` is admissible (`adm_pairT`), so its
  lattice sequence converges by `SepConv`. The rest of `LinkTS` is `LinkHS`.
* **hSM, hH, the `UniformBoundF` half of ApertureConv** at the observer `obsX`, whose transfer gap is
  the one `RunSeed N` gives (`LocalLink.observerGapAt_of_runSeed`): `obsX_SM` (by definition),
  `obsX_gap` (self-adjoint generator), `uniformBoundF_energy0`.

## The capstone

`clayStatementAt_of_inputs`. At `D = SymPlaqClass N`, `τ = 0`, `X = obsX`, `ρ = mixOfZ B op m Z`.

| input of `clayStatementAt_of_link` | discharged by | residual (typed) |
|---|---|---|
| `hSM` | `obsX_SM` (definition of `observerOSDataSLinked`) | none |
| `hH` | `obsX_gap` (`hamiltonianGap_of_selfAdjoint`, `observer_generator_isSelfAdjoint`), gap from `RunSeed N` | none beyond the observer inputs |
| `hRie` | `riemann_mixOfZ` | `CoefRiemann m` (data) |
| `hTie` | `scalarTie_mixOfZ` | `htr`, `hop` (data); `hZtie : κ Z_k(op b0) a_k⁴ → N/8` |
| `hConv` | `sepConv_mixOfZ` | `DiagBoundSep` at `Z` (local route); `hZ : Z k (O.refl 0) = Z k O` (also used by `h0`, `h1`) |
| `h0` | `os0Sep_mixOfZ` | `OS0Own hN op Z` |
| `h1` | `os1Sep_mixOfZ` (dyadic part proved) | `TransContT` |
| `hCov` | — | `TensorCov` |
| `hL` | `linkTS_of_hs` (the convergence of `ΘP ∪ Q`) | `LinkHS` |
| `hnt` | — | the non-zero vector of `HL ⊖ Ω` |
| `hK`, `hAF` | — | `TwoPointKernel G`, `AFCoefficient N G` |
| `hNG`, `hND` | — | `NonGaussianT`, `TensorNondeg` |
| `hAC` | `uniformBoundF_energy0` (first half) | `hCut`, the cut-off limit in `schwSFM` (proved from `hU` in `CutSU`) |
| `C`, `wC` | — | `Cs : Composites N`, `wC` (data) |
| `hCT` | — | `ChannelTie (mixOfZ B op m Z) Mb Zc ∧ TopNorm N Zc` for some `Mb`, `Zc` |
| `hWard` | — | `WardT` |
| `hCD` | — | `CompData Cs` |
| `hCO` | — | `CompOS Cs` |
| `hLC` | — | `LinkC obsX Cs wC` |
| `hTI` | — | `TIn (mixOfZ B op m Z) Cs obsX w wC` |
| `hGen` | `obsX_obsGen` (`ClayStatement.obsGen_observer`: `gvecT`, `flow_reconstruction`, `span_single_dense`) | none |

The local route's input `DiagBoundSep` at `zOwn` is `ApertureFinal.diagBoundSep_zOwn_of_nearOwn`
(`NearOwn`), at `N = 2` `diagBoundSep_zOwn_two` (`NearWin`, `PhysDefect`); at `N = 2` the same
`PhysDefect` gives `RunSeed 2` (`runSeed_two`).

## What `DiagBoundSep` does not give

* **OS0Sep.** `DiagBoundSep` and `NearOwn` give, per monomial, some constant; `OS0Sep` asks one
  `α, γ, β, κ` and the kernel form `α γⁿ (n!)^β d^{−κn} ∏ ‖cᵢ‖₁ ‖fᵢ‖_{L¹}`. `NearOwn` bounds point
  readings by `C(n, L, d) a^{8n} ∏ own readings`, and the form needs
  `C(n, L, d) ≤ α γⁿ (n!)^β d^{−κn}`, which `NearOwn` does not state, so `OS0Own` (the form on the
  basis readings) is new; `abs_contT_mixOfZ_le` transfers it from the basis to the sector.
* **The composites, the channel tie and the Ward identity** (`hCT`, `hWard`, `hCD`, `hCO`, `hLC`,
  `hTI`). The channel tie asks `m α b · Z k (op b) = ∑_β Zc k α β Mb β b` with `Zc k` acting on the
  tensor index and `Mb` step-independent; the per-field factor `Z k (op b)` carries the step dependence
  on the basis index instead, and the local route states no factorisation through the tensor index,
  no Ward identity and no datum on the composites.
* **The tie.** `zOwn` normalises each field by its own reading at `s₀`; `ScalarTie` pins the trace at
  the bare normalisation. They agree up to the constant `κ` exactly when `zOwn_k(O) a_k⁴` has a
  positive limit, which is `hZtie`.
* **LinkHS.** `contTransferSep` at `Z` (from `PairBoundSep`, from `DiagBoundSep`) supplies a GNS space
  with the Gram identity `⟪vecOfSep P, vecOfSep Q⟫ = kernSep P Q` and the shift intertwining, on
  monomials of lattice fields with per-field reflection `O.refl τ`. The tensor-level vectors `w P`
  need in addition: the basis to be reflection covariant (the reflected basis field `(op b).refl τ`
  carries the signed coefficient `reflC`), an isometry of that space into `X.base.H` intertwining the
  local shift with `X.base.time` (`LocalLink.LocalEmbedOn`), the empty monomial sent to
  `X.base.vac`, and the cross inner product with the flowed vectors `X.cvec Q`. None of the four is
  supplied by the local route.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the reflection plane and time axis, the reference step, the signs and the
excluded colour count; `1` the window of the observer's gap; `2` the least colour count, the square
of the factorial and the diameter factor; `4` the dimension; `8` the bare normalisation of
`ScalarTie`.
-/

noncomputable section

namespace MassGap.ClayWiring

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement Filter
open scoped Topology Matrix

variable {N : ℕ}

/-! ## 1. The mixing of a per-field factor -/

section Mix

variable {B : Type} [Fintype B]

/-- **The mixing with constant coefficients and a per-field factor**: `M k α b = m α b · Z k (op b)`.

DERIVED: no numeral. -/
def mixOfZ (B : Type) [Fintype B] (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) : RenormMix N where
  B := B
  fB := ‹Fintype B›
  op := op
  M := fun k α b => m α b * Z k (op b)

/-- The constant coefficient of the basis field `b` in `∑ c_α T_α`. DERIVED: no numeral. -/
def coefC (m : Idx4 → B → ℝ) (c : Idx4 → ℝ) (b : B) : ℝ := ∑ α, c α * m α b

/-- DERIVED: no numeral. -/
theorem mixC_mixOfZ (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (k : ℕ) (c : Idx4 → ℝ) (b : B) :
    mixC (mixOfZ B op m Z) k c b = coefC m c b * Z k (op b) := by
  show ∑ α, c α * (m α b * Z k (op b)) = (∑ α, c α * m α b) * Z k (op b)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun α _ => by ring

/-- **The sector's reading is a constant combination of the local route's readings.**

DERIVED: no numeral. -/
theorem latT_mixOfZ (hN : N ≠ 0) (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → TDatum) :
    latT hN (mixOfZ B op m Z) k F = ∑ b : ι → B, (∏ i, coefC m (F i).1 (b i))
      * latSkR hN (Renorm.connected hN Z) k (fun i => (op (b i), (F i).2)) := by
  unfold latT
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.prod_congr rfl fun i _ => mixC_mixOfZ op m Z k (F i).1 (b i), Finset.prod_mul_distrib,
    mul_assoc]
  rfl

/-- **The limit exists on admissible families from E on the reflection diagonal at `Z`.**

DERIVED: `0` the reflection plane. -/
theorem tendsto_latT_mixOfZ (hN : N ≠ 0) (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0) {ι : Type} [Fintype ι]
    [DecidableEq ι] (F : ι → TDatum) (hF : Adm F) :
    Tendsto (fun k => latT hN (mixOfZ B op m Z) k F) (ultra : Filter ℕ)
      (𝓝 (∑ b : ι → B, (∏ i, coefC m (F i).1 (b i))
        * contS hN (Renorm.connected hN Z) (fun i => (op (b i), (F i).2)))) := by
  obtain ⟨-, d, hd, hsep⟩ := hF
  have hR := Renorm.connected_reflCompat hN Z 0 hZ
  have hDC : ContinuumSepClass.DiagBoundClassAlong hN (dyBeta (one_le_of_ne_zero hN))
      (Renorm.connected hN Z) 0 ContinuumSepClass.TestClass.all := fun P => hD P.1
  have hT : ∀ b : ι → B, Tendsto
      (fun k => latSkR hN (Renorm.connected hN Z) k (fun i => (op (b i), (F i).2)))
      (ultra : Filter ℕ) (𝓝 (contS hN (Renorm.connected hN Z) (fun i => (op (b i), (F i).2)))) :=
    fun b => ClayTiltedFull.tendsto_contSAlong_of_diagBoundClass hN _ _ hR hDC _ hd
      (fun i j hij => hsep i j hij) (fun _ => trivial)
  have e : (fun k => latT hN (mixOfZ B op m Z) k F) = fun k => ∑ b : ι → B,
      (∏ i, coefC m (F i).1 (b i))
        * latSkR hN (Renorm.connected hN Z) k (fun i => (op (b i), (F i).2)) :=
    funext fun k => latT_mixOfZ hN op m Z k F
  rw [e]
  exact tendsto_finsetSum _ fun b _ => (hT b).const_mul _

/-- **The value on an admissible family.** DERIVED: `0` the reflection plane. -/
theorem contT_mixOfZ (hN : N ≠ 0) (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0) {ι : Type} [Fintype ι]
    [DecidableEq ι] (F : ι → TDatum) (hF : Adm F) :
    contT hN (mixOfZ B op m Z) F = ∑ b : ι → B, (∏ i, coefC m (F i).1 (b i))
        * contS hN (Renorm.connected hN Z) (fun i => (op (b i), (F i).2)) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  unfold contT
  exact (tendsto_latT_mixOfZ hN op m Z hZ hD F hF).limUnder_eq

/-- **`SepConv` from `DiagBoundSep` at `Z`.** DERIVED: `0` the reflection plane. -/
theorem sepConv_mixOfZ (hN : N ≠ 0) (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0) :
    SepConv hN (mixOfZ B op m Z) := by
  intro ι _ _ F hF
  rw [contT_mixOfZ hN op m Z hZ hD F hF]
  exact tendsto_latT_mixOfZ hN op m Z hZ hD F hF

/-- The Riemann symmetries of the constant coefficients. DERIVED: no numeral. -/
def CoefRiemann (m : Idx4 → B → ℝ) : Prop :=
  ∀ α b, m (swap01 α) b = -m α b ∧ m (swap23 α) b = -m α b ∧ m (pairEx α) b = m α b

/-- DERIVED: no numeral. -/
theorem riemann_mixOfZ (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (h : CoefRiemann m) : (mixOfZ B op m Z).Riemann := by
  intro k α b
  obtain ⟨h1, h2, h3⟩ := h α b
  refine ⟨?_, ?_, ?_⟩
  · show m (swap01 α) b * Z k (op b) = -(m α b * Z k (op b))
    rw [h1]; ring
  · show m (swap23 α) b * Z k (op b) = -(m α b * Z k (op b))
    rw [h2]; ring
  · show m (pairEx α) b * Z k (op b) = m α b * Z k (op b)
    rw [h3]

/-- **The scalar tie from the trace coefficients.** The trace has coefficient `κ` on the basis field
`op b0 = sym (plaqField q0)` and `0` on the others; the tie is then `κ Z_k(op b0) a_k⁴ → N/8`.

DERIVED: `8`, `4` as in `ScalarTie`; `0` the other coefficients. -/
theorem scalarTie_mixOfZ [DecidableEq B] (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (b0 : B) (κ : ℝ)
    (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0))
    (hlim : Tendsto (fun k => κ * Z k (op b0) * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8))) :
    ScalarTie (mixOfZ B op m Z) (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)) := by
  refine ⟨rfl, fun k => κ * Z k (op b0), fun k => ?_, hlim⟩
  show ∑ b : B, mixC (mixOfZ B op m Z) k trC b • (op b).1 = (κ * Z k (op b0)) • _
  rw [Finset.sum_eq_single b0]
  · rw [mixC_mixOfZ, htr, if_pos rfl]
    exact congrArg (fun O : LField (MassGap.SUN.SU N) => (κ * Z k (op b0)) • O.1) hop
  · intro b _ hb
    rw [mixC_mixOfZ, htr, if_neg hb, zero_mul, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ b0) h

end Mix

/-! ## 2. OS0 from the basis readings -/

section OS0

variable {B : Type} [Fintype B]

/-- **OS0 on the basis readings at `Z`, the kernel bound**: one `α, γ, β, κ` with
`|S((op bᵢ, fᵢ))| ≤ α γⁿ (n!)^β d^{−κn} ∏ᵢ ‖fᵢ‖_{L¹}` on `d`-separated families of continuous test
functions, `0 < d ≤ 1`.

DERIVED: `1`, `0` as in `OS0Sep`. -/
def OS0Own (hN : N ≠ 0) (op : B → LField (MassGap.SUN.SU N))
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) : Prop :=
  ∃ α γ β κ : ℝ, ∀ (n : ℕ) (b : Fin n → B) (f : Fin n → TestFn) (d : ℝ), 0 < d → d ≤ 1 →
    (∀ i, Continuous (f i).1) → (∀ i j, i ≠ j → ContinuumSep.sepBy d (f i) (f j)) →
      |contS hN (Renorm.connected hN Z) (fun i => (op (b i), f i))|
        ≤ α * γ ^ n * (n.factorial : ℝ) ^ β * (d ^ (κ * n))⁻¹ * ∏ i, l1 (f i)

/-- `|coefC m c b| ≤ ‖c‖₁ ∑|m|`. DERIVED: no numeral. -/
theorem abs_coefC_le (m : Idx4 → B → ℝ) (c : Idx4 → ℝ) (b : B) :
    |coefC m c b| ≤ cnorm c * ∑ α, ∑ b', |m α b'| := by
  unfold coefC cnorm
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun α _ => ?_
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc |m α b| ≤ ∑ b', |m α b'| :=
        Finset.single_le_sum (f := fun b' => |m α b'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ b)
    _ ≤ ∑ α', ∑ b', |m α' b'| :=
        Finset.single_le_sum (f := fun α' => ∑ b', |m α' b'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ α)

/-- **Any bound on the basis readings transfers to the sector**: if every reading
`|S((op bᵢ, fᵢ))|` of an admissible family is at most `T`, then
`|S(F)| ≤ (|B| ∑|m|)^{|ι|} ∏ᵢ ‖cᵢ‖₁ · T`. The form of `T` (a `d^{−4n}` or an `L¹` kernel bound) is
the caller's.

DERIVED: `0` the reflection plane. -/
theorem abs_contT_mixOfZ_le (hN : N ≠ 0) (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0) {ι : Type} [Fintype ι]
    [DecidableEq ι] (F : ι → TDatum) (hF : Adm F) (T : ℝ)
    (hS : ∀ b : ι → B, |contS hN (Renorm.connected hN Z) (fun i => (op (b i), (F i).2))| ≤ T) :
    |contT hN (mixOfZ B op m Z) F|
      ≤ ((Fintype.card B : ℝ) * ∑ a, ∑ b', |m a b'|) ^ Fintype.card ι * (∏ i, cnorm (F i).1) * T := by
  obtain ⟨mx, hmx⟩ : ∃ mx : ℝ, mx = ∑ a, ∑ b', |m a b'| := ⟨_, rfl⟩
  have hmx0 : 0 ≤ mx := hmx ▸ Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hc0 : ∀ i, 0 ≤ cnorm (F i).1 := fun i => Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [contT_mixOfZ hN op m Z hZ hD F hF, ← hmx]
  calc |∑ b : ι → B, (∏ i, coefC m (F i).1 (b i))
          * contS hN (Renorm.connected hN Z) (fun i => (op (b i), (F i).2))|
      ≤ ∑ b : ι → B, |(∏ i, coefC m (F i).1 (b i))
          * contS hN (Renorm.connected hN Z) (fun i => (op (b i), (F i).2))| :=
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

/-- **`OS0Sep` from `OS0Own`**, with `α' = |α|`, `γ' = |γ| · |B| · ∑|m|` and the same `β, κ`.

DERIVED: `0` the reflection plane. -/
theorem os0Sep_mixOfZ (hN : N ≠ 0) (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0) (h0 : OS0Own hN op Z) :
    OS0Sep hN (mixOfZ B op m Z) := by
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
      |contS hN (Renorm.connected hN Z) (fun i => (op (b i), (F i).2))| ≤ |α| * |γ| ^ n * K :=
    fun b => by
      have h := hαγ n b (fun i => (F i).2) d hd hd1 hc hs
      calc _ ≤ _ := h
        _ = (α * γ ^ n) * K := by rw [hK]; ring
        _ ≤ |α * γ ^ n| * K := mul_le_mul_of_nonneg_right (le_abs_self _) hK0
        _ = |α| * |γ| ^ n * K := by rw [abs_mul, abs_pow]
  have hb := abs_contT_mixOfZ_le hN op m Z hZ hD F hF _ hS
  rw [← hmx, Fintype.card_fin] at hb
  refine hb.trans (le_of_eq ?_)
  rw [hK]
  simp only [Finset.prod_mul_distrib, mul_pow]
  ring

end OS0

/-! ## 3. Translations -/

section Translation

variable {B : Type} [Fintype B]

/-- An admissible family stays admissible under a translation. DERIVED: no numeral. -/
theorem adm_translate {ι : Type} {F : ι → TDatum} (hF : Adm F) (v : Fin 4 → ℝ) :
    Adm (fun i => translateD v (F i)) := by
  obtain ⟨hc, d, hd, hs⟩ := hF
  exact ⟨fun i => (hc i).comp (continuous_id.sub continuous_const), d, hd,
    fun i j hij => ContinuumSep.sepBy_translate (hs i j hij) v⟩

/-- **OS1 at the dyadic translations, with no hypothesis**: from step `j` on, `site a_j p` is a lattice
translation and the Wilson state is invariant under it.

DERIVED: no numeral. -/
theorem contT_translate_dyadic (hN : N ≠ 0) (op : B → LField (MassGap.SUN.SU N))
    (m : Idx4 → B → ℝ) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (F : ι → TDatum) (j : ℕ) (p : ISite) :
    contT hN (mixOfZ B op m Z) (fun i => translateD (site (dySpacing N j) p) (F i))
      = contT hN (mixOfZ B op m Z) F := by
  unfold contT
  refine limUnder_congr_ultra ?_
  filter_upwards [eventually_ge_atTop j] with k hk
  rw [latT_mixOfZ hN op m Z k, latT_mixOfZ hN op m Z k]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  exact ClayTiltedFull.latSkRAlong_translate hN (dyBeta (one_le_of_ne_zero hN))
    (Renorm.connected hN Z) (fun i => (op (b i), (F i).2)) hk p

/-- **The dyadic vectors approximate every vector**: `a_j ⌊v/a_j⌋ → v`.

DERIVED: `4` the dimension; `1` the floor's width. -/
theorem tendsto_dyadic_approx (hN : N ≠ 0) (v : Fin 4 → ℝ) :
    Tendsto (fun j : ℕ => site (dySpacing N j) (fun μ => ⌊v μ / dySpacing N j⌋)) atTop (𝓝 v) := by
  rw [tendsto_pi_nhds]
  intro μ
  have ha : ∀ j, 0 < dySpacing N j := dySpacing_pos (one_le_of_ne_zero hN)
  have hb : ∀ j, v μ - dySpacing N j ≤ dySpacing N j * (⌊v μ / dySpacing N j⌋ : ℝ)
      ∧ dySpacing N j * (⌊v μ / dySpacing N j⌋ : ℝ) ≤ v μ := fun j => by
    have h1 := Int.floor_le (v μ / dySpacing N j)
    have h2 := Int.lt_floor_add_one (v μ / dySpacing N j)
    have e : dySpacing N j * (v μ / dySpacing N j) = v μ := by
      have := (ha j).ne'
      field_simp
    have h3 := mul_le_mul_of_nonneg_left h1 (ha j).le
    have h4 := mul_lt_mul_of_pos_left h2 (ha j)
    constructor <;> nlinarith
  have hlow : Tendsto (fun j => v μ - dySpacing N j) atTop (𝓝 (v μ)) := by
    have := (tendsto_const_nhds (x := v μ)).sub (tendsto_dySpacing N)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun j => (hb j).1)
    (fun j => (hb j).2)

/-- **Continuity of the continuum function in a common real translation.**

DERIVED: `4` the dimension. -/
def TransContT (hN : N ≠ 0) (ρ : RenormMix N) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → TDatum), Adm F →
    Continuous (fun v : Fin 4 → ℝ => contT hN ρ (fun i => translateD v (F i)))

/-- **`OS1Sep` from `DiagBoundSep` at `Z` and continuity in the translation.**

DERIVED: `0` the reflection plane. -/
theorem os1Sep_mixOfZ (hN : N ≠ 0) (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0)
    (hTC : TransContT hN (mixOfZ B op m Z)) : OS1Sep hN (mixOfZ B op m Z) := by
  intro ι _ _ F hF v
  have hconv := sepConv_mixOfZ hN op m Z hZ hD ι _ (adm_translate hF v)
  have hc := ((hTC ι F hF).tendsto v).comp (tendsto_dyadic_approx hN v)
  have hc' : Tendsto (fun _ : ℕ => contT hN (mixOfZ B op m Z) F) atTop
      (𝓝 (contT hN (mixOfZ B op m Z) (fun i => translateD v (F i)))) :=
    hc.congr fun j => contT_translate_dyadic hN op m Z F j _
  have heq := tendsto_nhds_unique hc' tendsto_const_nhds
  rw [← heq]
  exact hconv

end Translation

/-! ## 4. The link: what the convergence of `SepConv` supplies -/

section Link

variable {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4} {r : ℝ}

/-- **`ΘP ∪ Q` is admissible.** Its separation is `ContinuumSep.famSep_pairFam_exists` on the
monomials with the same test functions.

DERIVED: `4` the dimension. -/
theorem adm_pairT (P Q : TSep τ) : Adm (pairT τ P.1 Q.1) := by
  obtain ⟨hcP, dP, hdP, hP⟩ := P.2
  obtain ⟨hcQ, dQ, hdQ, hQ⟩ := Q.2
  let O0 : LField (MassGap.SUN.SU 2) := sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)
  let P' : Mono 2 := ⟨P.1.1, fun i => (O0, (P.1.2 i).2)⟩
  let Q' : Mono 2 := ⟨Q.1.1, fun i => (O0, (Q.1.2 i).2)⟩
  obtain ⟨d, hd, hs⟩ := ContinuumSep.famSep_pairFam_exists (τ := τ) (P := P') (Q := Q')
    ⟨dP, hdP, hP⟩ ⟨dQ, hdQ, hQ⟩
  have hr : Continuous (reflR τ) := continuous_id.update τ (continuous_apply τ).neg
  refine ⟨fun i => ?_, d, hd, fun i j hij => ?_⟩
  · rcases i with a | a
    · exact (hcP a).comp hr
    · exact hcQ a
  · have h := hs i j hij
    rcases i with a | a <;> rcases j with b | b <;> exact h

/-- **The link without its convergence clause**: the Gram identity, the shift as `X.base.time`, the
local vacuum, and the cross reading with the flowed vectors.

DERIVED: `4` the dimension. -/
def LinkHS (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (X : OSDataSLinked N D τ r) (ρ : RenormMix N) (w : TSep τ → X.base.H) : Prop :=
  (∀ P Q : TSep τ, inner ℂ (w P) (w Q) = (kernT hN ρ τ P Q : ℂ))
    ∧ (∀ (m : ℕ) (P : TSep τ), w (shiftT hN τ m P) = X.base.time (dySpacing N m) (w P))
    ∧ w (emptyT τ) = X.base.vac
    ∧ ∀ (P : TSep τ) (Q : MarginMonoD N D τ r),
        Tendsto (fun k => mixLatT hN ρ (energy0 W D hD) τ k P.1 Q.1.1) (ultra : Filter ℕ)
            (𝓝 (mixT hN ρ (energy0 W D hD) τ P.1 Q.1.1))
          ∧ inner ℂ (w P) (X.cvec Q) = (mixT hN ρ (energy0 W D hD) τ P.1 Q.1.1 : ℂ)

/-- **`LinkTS` from `SepConv` and `LinkHS`.** DERIVED: no numeral. -/
theorem linkTS_of_hs (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (X : OSDataSLinked N D τ r) (ρ : RenormMix N) (w : TSep τ → X.base.H) (hC : SepConv hN ρ)
    (h : LinkHS hN W D hD X ρ w) : LinkTS hN W D hD X ρ w :=
  ⟨fun P Q => ⟨hC _ (pairT τ P.1 Q.1) (adm_pairT P Q), h.1 P Q⟩, h.2.1, h.2.2.1, h.2.2.2⟩

end Link

/-! ## 5. The observer with the gap of the run seed -/

section Observer

/-- The transfer gap at step `0` that `RunSeed N` supplies. DERIVED: `0` the plane and the step. -/
theorem gapEx (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N))
      (uniformBoundF_energy0 hN W (SymPlaqClass N) (symPlaq_refl N) (symPlaq_nonneg hN)
        (symPlaq_cube hN W hW hcube)) 0 hphys 0) ρ :=
  LocalLink.observerGapAt_of_runSeed hN2 hN hfar _ _ hphys 0

/-- **The observer at the field `sym (plaqField q0)`, with the gap of the run seed.**

DERIVED: `0` the plane and the step; `1` the window. -/
def obsX (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W (SymPlaqClass N) t C)
    (hUE : UnitCubeExpBound hN W (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)))
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N) : OSDataSLinked N (SymPlaqClass N) 0 r :=
  observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN) (symPlaq_cube hN W hW hcube) ht hC0
    hU (O := sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0))
    ⟨ObserverEnergyMoments.q0, rfl⟩ hUE 0 hphys 0 one_pos
    (Classical.choose_spec (gapEx hN2 hN W hW hcube hphys hfar)).1
    (Classical.choose_spec (gapEx hN2 hN W hW hcube hphys hfar)).2.1
    (Classical.choose_spec (gapEx hN2 hN W hW hcube hphys hfar)).2.2 hNT

/-- **The Hamiltonian gap of the observer**, from its self-adjoint generator; the gap is the one the
run seed gives. DERIVED: `0` the plane. -/
theorem obsX_gap (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W (SymPlaqClass N) t C)
    (hUE : UnitCubeExpBound hN W (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)))
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N) :
    HamiltonianGap (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).base :=
  hamiltonianGap_of_selfAdjoint _
    (observer_generator_isSelfAdjoint hN (energy0 W (SymPlaqClass N) (symPlaq_refl N))
      (uniformBoundF_energy0 hN W (SymPlaqClass N) (symPlaq_refl N) (symPlaq_nonneg hN)
        (symPlaq_cube hN W hW hcube)) 0
      (Flow.posPreserving_of_physRange hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hphys 0))

/-- **The observer's functional is `schwSFM`**, by definition. DERIVED: no numeral. -/
theorem obsX_SM (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W (SymPlaqClass N) t C)
    (hUE : UnitCubeExpBound hN W (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)))
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N) :
    ∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (g : ι → Decaying),
      (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).SM O g
        = schwSFM hN W (SymPlaqClass N) (symPlaq_refl N) O g :=
  fun _ _ _ _ => rfl

/-- **The observer carries its Hilbert space** (`ClayStatement.obsGen_observer`).

DERIVED: `0` the plane and the step; `1` the window. -/
theorem obsX_obsGen (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W (SymPlaqClass N) t C)
    (hUE : UnitCubeExpBound hN W (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)))
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N) :
    ObsGen hN W (SymPlaqClass N) (symPlaq_refl N)
      (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar) :=
  obsGen_observer hN W (symPlaq_refl N) (symPlaq_nonneg hN) (symPlaq_cube hN W hW hcube) ht hC0
    hU (O := sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0))
    ⟨ObserverEnergyMoments.q0, rfl⟩ hUE 0 hphys 0 one_pos
    (Classical.choose_spec (gapEx hN2 hN W hW hcube hphys hfar)).1
    (Classical.choose_spec (gapEx hN2 hN W hW hcube hphys hfar)).2.1
    (Classical.choose_spec (gapEx hN2 hN W hW hcube hphys hfar)).2.2 hNT

/-- The observer's field is `sym (plaqField q0)`. DERIVED: no numeral. -/
theorem obsX_O (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W (SymPlaqClass N) t C)
    (hUE : UnitCubeExpBound hN W (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)))
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N) :
    (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).O
      = sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0) :=
  rfl

end Observer

/-! ## 6. The capstone -/

section Capstone

/-- **`ClayStatementAt` from the observer's inputs, the run seed, the local route's `DiagBoundSep`, the
mixing data, and the residuals.** See the module docstring for the table.

Observer inputs: `hW`, `hcube`, `ht`, `hC0`, `hU`, `hUE`, `hphys`, `hNT` (those of
`clayFullAt_of_observer`; `ObserverMoments.observer_moment_inputs_of_classUnitExp` gives `hcube`, `hU`,
`hUE` from one `ClassUnitExp`). Far input: `hfar : RunSeed N`. Local route: `hZ`, `hD`. Mixing data:
`op`, `m`, `hRie`, `b0`, `κ`, `htr`, `hop`. Composite data: `Cs`, `wC`. Residuals: `hZtie`, `h0`, `hTC`,
`hCov`, `hK`, `hAF`, `hNG`, `hND`, `hCut`, `hL`, `hnt`, `hCT`, `hWard`, `hCD`, `hCO`, `hLC`, `hTI`.
`CutSU.cut_of_classMoments` proves `hCut` from `ht`, `hC0`, `hU`; `CutSU.clayStatementAt_of_inputs'` is
this theorem without it. `SUInputs.clayStatementAt_of_inputs''` is this theorem without `hCut`, `hW`,
`hcube`, `hC0`, `hUE`, `hnt`; `TransContSU.clayStatementAt_of_inputs_TC` is that one without `hTC`
(`transContT_of_os0`, from `hZ`, `hD`, `h0`).

DERIVED: `2` the least colour count; `0` the plane, the vanishing pairing and the zero vector; `8`,
`4` as in `ScalarTie`. -/
theorem clayStatementAt_of_inputs (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N)
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
    (G : ℝ → ℝ) (hK : TwoPointKernel hN (mixOfZ B op m Z) G) (hAF : AFCoefficient N G)
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
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  have hConv := sepConv_mixOfZ hN op m Z hZ hD
  clayStatementAt_of_link hN2 W (SymPlaqClass N) (symPlaq_refl N)
    (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar) (mixOfZ B op m Z) G w
    (obsX_SM hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar)
    (obsX_gap hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar)
    (riemann_mixOfZ op m Z hRie)
    (scalarTie_mixOfZ op m Z b0 κ htr hop hZtie)
    hConv (os0Sep_mixOfZ hN op m Z hZ hD h0) (os1Sep_mixOfZ hN op m Z hZ hD hTC) hCov
    (linkTS_of_hs hN W (SymPlaqClass N) (symPlaq_refl N) _ (mixOfZ B op m Z) w hConv hL)
    hnt hK hAF hNG hND
    ⟨uniformBoundF_energy0 hN W (SymPlaqClass N) (symPlaq_refl N) (symPlaq_nonneg hN)
      (symPlaq_cube hN W hW hcube), hCut⟩
    Cs wC hCT hWard hCD hCO hLC hTI (obsX_obsGen hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar)

/-- **The local route's `DiagBoundSep` at `zOwn` at `SU(2)`**, from its two inputs (`clay_two`).

DERIVED: `2` the rank; `8` `clay_two`'s window; `0` the plane; `1/1000` the seed defect. -/
theorem diagBoundSep_zOwn_two {M₀ : ℕ} {s₀ L : ℝ} (hs₀ : 0 < s₀)
    (h8 : 8 * (s₀ + s₀) < M₀ * AsymptoticScaling.aRun 2 1) (hL : 0 < L)
    (hNear : ApertureVolume.NearWin two_ne_zero (dyBeta (one_le_of_ne_zero two_ne_zero)) M₀ s₀)
    (hW : ApertureBridge.PhysDefect L (1 / 1000)) :
    ContinuumSep.DiagBoundSep two_ne_zero
      (Renorm.connected two_ne_zero (ExistenceReduceOwn.zOwn two_ne_zero s₀ s₀)) 0 := by
  obtain ⟨hD, -⟩ := ApertureVolume.clay_two two_ne_zero hs₀ h8 hL hNear hW
  exact hD

/-- **The run seed at `SU(2)`** from the local route's far input. DERIVED: `2` the rank;
`1/1000` the seed defect. -/
theorem runSeed_two {L : ℝ} (hL : 0 < L) (hW : ApertureBridge.PhysDefect L (1 / 1000)) :
    WDeltaRun.RunSeed 2 :=
  ApertureBridge.runSeed_of_physDefect hL hW

end Capstone

end MassGap.ClayWiring

end

#print axioms MassGap.ClayWiring.mixC_mixOfZ
#print axioms MassGap.ClayWiring.latT_mixOfZ
#print axioms MassGap.ClayWiring.tendsto_latT_mixOfZ
#print axioms MassGap.ClayWiring.contT_mixOfZ
#print axioms MassGap.ClayWiring.sepConv_mixOfZ
#print axioms MassGap.ClayWiring.riemann_mixOfZ
#print axioms MassGap.ClayWiring.scalarTie_mixOfZ
#print axioms MassGap.ClayWiring.abs_coefC_le
#print axioms MassGap.ClayWiring.abs_contT_mixOfZ_le
#print axioms MassGap.ClayWiring.os0Sep_mixOfZ
#print axioms MassGap.ClayWiring.adm_translate
#print axioms MassGap.ClayWiring.contT_translate_dyadic
#print axioms MassGap.ClayWiring.tendsto_dyadic_approx
#print axioms MassGap.ClayWiring.os1Sep_mixOfZ
#print axioms MassGap.ClayWiring.adm_pairT
#print axioms MassGap.ClayWiring.linkTS_of_hs
#print axioms MassGap.ClayWiring.gapEx
#print axioms MassGap.ClayWiring.obsX_gap
#print axioms MassGap.ClayWiring.obsX_SM
#print axioms MassGap.ClayWiring.obsX_O
#print axioms MassGap.ClayWiring.clayStatementAt_of_inputs
#print axioms MassGap.ClayWiring.diagBoundSep_zOwn_two
#print axioms MassGap.ClayWiring.runSeed_two
