import Mathlib
import MassGap.ClayTreeG
import MassGap.MeasuredTower

/-!
# MassGap.ClayStatementG — the Clay statement over a compact simple gauge group `G`

`ClayStatement.ClayStatementAt` with `SU(N)` replaced by a group `G` carrying `GaugeGroup`
(compact, Borel, a faithful unitary plaquette representation `ρ : G → U(d)`), `GaugeSimple`
(`dim 𝔤`, `h^∨`, `T(ρ)`) and `GaugeLie` (the Hermitian generators of `ρ(𝔤)`). The clauses are those
of `ClayStatement`, word for word, on the `G` objects of `ClayTreeG`.

## The root

`ClayStatementOf G`: some measured tower `βs` (`MeasuredTower.MeasTowerG`: `βs → ∞`, and for one unit
`c > 0` and all large `k` the tensor channel's measured mass at `βs k` lies in `[c a_k, 2c a_k]`), some
configuration flow `W` and some reflection-closed class `D` with `ClayStatementAtP (schedAlongG G βs)
(constsG G) W D`: the periodic Wilson state of `G` at `βs k`, read at the dyadic spacing `a_k = dySpacingG G k`.
`MassGap.ClayStatement` is `ClayStatementSU N` (`ClayStatementOf (SU N)`) at every `N ≥ 2`
(`clayStatement_iff_SU`, `Iff.rfl`).

`ClayStatementOfDy G` is the statement at the frozen tower (`canonSched G`, the coupling `dyBetaG G k`
fixed by the two-loop running spacing): `ClayStatementAtG G W D`. `ClayStatementDy`
(`ClayStatement.lean`) is its `SU(N)` form at every `N ≥ 2` (`clayStatementDy_iff_SU`).

## Where `SU(N)` entered, and what replaces it

| `ClayStatement` at `SU(N)` | `ClayStatementAtG G` |
|---|---|
| configurations `ℤ⁴ → SU(N)`, Haar, `wilsonDensity` | `IConf G`, `probHaar G`, `wilsonDensityG G` (`1 − Re tr ρ(g)/d`) |
| `stateK`, `dySpacing N` (`aRun N`, `b₀ = 11N/(48π²)`) | `canonSched G`: `periodicStateG G`, `dySpacingG G` (`aRunG G`, `b₀ = 11h^∨/(48π²)`) |
| `A_μ(x)` Hermitian traceless `N × N` | `A_μ(x)` `d × d` with `GaugeLie.lieGen` |
| `U = exp(i a g A)` in `SU(N) ⊆ U(N)` | `ρ(U) = exp(i a g A)` |
| `tr` the fundamental trace | `tr` the trace in `ρ` |
| `ScalarTie`: `Ztr a⁴ → N/8` | `d/(16 T(ρ))` |
| `TopNorm`: `zq a⁴ → 2` | `1/T(ρ)` |
| `AFCoefficient`: `12(N² − 1)/(π⁴ b₀²)` | `12 dim 𝔤/(π⁴ b₀²)` |

Each constant is the `SU(N)` one at `d = N`, `T = 1/2`, `dim 𝔤 = N² − 1`, `h^∨ = N`
(`constsG_SU`). The normalisations: a plaquette density is `a⁴ g² T(ρ) F^a F^a/(2d)` to leading
order (at `SU(N)`, `a⁴g²F^aF^a/(4N)`), so the bare `g₀² F^a F^a` is `d/(16 T a⁴)` times
`sym (plaqField q0)`; `F^a F̃^a = tr_ρ(F F̃)/T(ρ)`; the tree two-point function of `g² F^a F^a`
counts `dim 𝔤` gluons.

## The parametric statement

`ClayStatementAtP S K W D` is the statement at a schedule `S` (`ClayTreeG.Sched`) and constants
`K` (`ClayConsts`). `ClayStatementAtG G W D = ClayStatementAtP (canonSched G) (constsG G) W D`.

## The specialisation

* `clayStatementAtP_SU_iff`: `ClayStatementAtP (schedSU N) (constsSU N) W.toG D ↔
  ClayStatementAt hN2 W D hD`, for every `W : ConfFlow N` and reflection-closed `D`. Each witness
  passes field by field (`OSDataSLinked.toG`, `RenormMix.toG`, `Composites.toG` and back) and each
  clause is the `SU(N)` clause by definition.
* `clayStatementAtG_SU_iff`: the same with `canonSched (SU N)` and `constsG (SU N)`, through
  `canonSched_SU` and `constsG_SU`.
* `clayStatementOfDy_SU_iff`, `clayStatementDy_iff_SU`: `ClayStatementDy` is
  `∀ N ≥ 2, ClayStatementSUDy N`.

So the frozen-tower `G` form at `SU(N)` is `ClayStatementDy`, clause for clause.

## The capstone

`clayStatementAtP_of_link` mirrors `ClayStatement.clayStatementAt_of_link`: from the same inputs
(`hSM`, `hH`, `hRie`, `hTie`, `hConv`, `h0`, `h1`, `hCov`, `hL`, `hnt`, `hK`, `hAF`, `hNG`, `hND`,
`hAC`, `hCT`, `hWard`, `hCD`, `hCO`, `hLC`, `hTI`, `hGen`), stated on the `G` objects, OS3, OS2, OS4, the
two spectral clauses, `AFShortDistance` and the non-zero vector of `HLC` are proved, at every
schedule and every `K` with `0 < K.cAF`. `clayStatementAtG_of_link` is it at `canonSched G`,
`constsG G` (`afConstG_pos`).

## The wiring of `ClayWiring`, over `G`

`ClayWiring.clayStatementAt_of_inputs` discharges inputs of the `SU(N)` capstone. Its steps split:

* **Group-generic** (they read only the mixing, the schedule's `a_k > 0`, `a_k → 0`, and the
  Hilbert-space data; `ClayWiringG` states and proves them over any schedule `S : Sched G`, with
  `stateK`, `dySpacing` replaced by `S.ν`, `S.a`, and assembles `clayStatementAtG_of_inputsG`):
  `mixOfZ`, `latT_mixOfZ`, `sepConv_mixOfZ` (given `DiagBoundSep`), `riemann_mixOfZ`,
  `scalarTie_mixOfZ` (with `N/8` replaced by `K.cTr`), `abs_contT_mixOfZ_le`, `os0Sep_mixOfZ`
  (given `OS0Own`), `adm_translate`, `tendsto_dyadic_approx`, `os1Sep_mixOfZ` (given the dyadic
  invariance), `adm_pairT`, `linkTS_of_hs`.
* **`SU(N)`-specific**, the residuals of the `G` capstone beyond those of `clayStatementAt_of_link`:
  the observer `obsX` with `obsX_SM`, `obsX_gap` (`hSM`, `hH`: the observer construction
  `observerOSDataSLinked`, `uniformBoundF_energy0`, `observer_generator_isSelfAdjoint`, the transfer
  gap from `RunSeed N`), the dyadic translation invariance `contT_translate_dyadic` (through
  `ClayTiltedFull.latSkRAlong_translate`, the shift invariance of the `SU(N)` periodic state; not
  stated for `periodicStateG`), the local route's `DiagBoundSep` (`ApertureFinal`, at `SU(2)`
  `diagBoundSep_zOwn_two`, `runSeed_two`).

## The statement over the instantiated groups

`ClayStatementClassical`: `ClayStatementOf` at `SU(N)` (`N ≥ 2`), `SO(n)` (`n ≥ 5`), `SO(3)` and
compact `Sp(n)` (`n ≥ 1`). `clayStatement_of_classical`: it implies `ClayStatement`.
`ClayStatementClassicalDy` is the same at the frozen tower; `clayStatementDy_of_classicalDy`: it implies
`ClayStatementDy`. The exceptional
groups are instantiated in their own modules as stabilisers of invariant tensors in compact matrix
groups: `GaugeG2` (the 3-form in `SO(7)`), `GaugeF4` (the Jordan cubic in `SO(26)`), `GaugeE6` (the
complex cubic norm in `SU(27)`), `GaugeE7` (Freudenthal's quartic in `Sp(28)`), `GaugeE8` (the
bracket in `SO(248)`), with `ClayStatementG2`, …, `ClayStatementE8` there.

## What the statement does not say

Everything in `ClayStatement`'s list, and: `GaugeSimple` and `GaugeLie` are entered per instance and
not derived from `G`; `ClayStatementOf` at a group is about the instances declared there.
-/

noncomputable section

namespace MassGap.ClayStatementG

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayTreeG Filter
open MassGap.MeasuredTower (MeasTowerG schedAlongG)
open scoped Topology Matrix

/-! ## 0. The normalisation constants -/

/-- **The three normalisation constants of the statement**: the scalar tie `cTr`, the topological
normalisation `cTop`, the asymptotic-freedom coefficient `cAF`.

DERIVED: no numeral. -/
structure ClayConsts where
  cTr : ℝ
  cTop : ℝ
  cAF : ℝ

/-- **The constants of `ClayStatement`**: `N/8`, `2`, `12(N² − 1)/(π⁴ b₀²)`.

DERIVED: `8`, `2` those of `ScalarTie` and `TopNorm`. -/
def constsSU (N : ℕ) : ClayConsts := ⟨(N : ℝ) / 8, 2, afConst N⟩

section Consts

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G]

/-- **The asymptotic-freedom coefficient of `G`**: `12 dim 𝔤/(π⁴ b₀²)`, `b₀ = 11h^∨/(48π²)`.

DERIVED: `12 = 48/4` as in `ClayStatement.afConst`; `4` the power of `π`; `2` the square. -/
def afConstG : ℝ :=
  12 * (GaugeSimple.lieDim (G := G) : ℝ) / (Real.pi ^ 4 * GaugeRunning.b0G G ^ 2)

/-- **The constants of `G`**: `d/(16 T(ρ))`, `1/T(ρ)`, `afConstG G`.

DERIVED: `16 = 8 · 2`, the `SU(N)` tie `N/8` at `T = 1/2`, `d = N`; `1` the numerator of `1/T`. -/
def constsG : ClayConsts :=
  ⟨GaugeRunning.dG G / (16 * GaugeRunning.TG G), 1 / GaugeRunning.TG G, afConstG G⟩

/-- DERIVED: `0` the sign. -/
theorem afConstG_pos [GaugeLie G] : 0 < afConstG G := by
  unfold afConstG
  have h1 : (0 : ℝ) < (GaugeSimple.lieDim (G := G) : ℝ) := Nat.cast_pos.mpr GaugeLie.lieDim_pos
  have h2 := GaugeRunning.b0G_pos (G := G)
  have h3 := Real.pi_pos
  positivity

end Consts

/-- **At `SU(N)` the constants of `G` are those of `ClayStatement`.**

DERIVED: `2` the least colour count; `1` the subtracted unit. -/
theorem constsG_SU (N : ℕ) [NeZero N] [Fact (2 ≤ N)] :
    constsG (MassGap.SUN.SU N) = constsSU N := by
  have h2 : 2 ≤ N := Fact.out
  have hN1 : 1 ≤ N ^ 2 := by nlinarith
  unfold constsG constsSU afConstG ClayStatement.afConst ClayStatement.b0
  have e1 : GaugeRunning.dG (MassGap.SUN.SU N) / (16 * GaugeRunning.TG (MassGap.SUN.SU N))
      = (N : ℝ) / 8 := by
    show (N : ℝ) / (16 * (1 / 2 : ℝ)) = (N : ℝ) / 8
    norm_num
  have e2 : 1 / GaugeRunning.TG (MassGap.SUN.SU N) = 2 := by
    show 1 / (1 / 2 : ℝ) = 2
    norm_num
  have e3 : ((GaugeSimple.lieDim (G := MassGap.SUN.SU N) : ℕ) : ℝ) = (N : ℝ) ^ 2 - 1 := by
    show ((N ^ 2 - 1 : ℕ) : ℝ) = (N : ℝ) ^ 2 - 1
    rw [Nat.cast_sub hN1]
    push_cast
    ring
  rw [e1, e2, e3]
  rfl

#print axioms constsG_SU

/-! ## 1. Classical configurations -/

section Classical

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G] [GaugeLie G]

/-- A gauge potential of `G`: `d × d` matrices, `d` the dimension of the plaquette representation.

DERIVED: no numeral. -/
abbrev GPotG (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] : Type :=
  GPot (GaugeGroup.dim G)

/-- **Admissible potential**: smooth, with values Hermitian generators of `ρ(𝔤)`.

DERIVED: no numeral. -/
def AdmPot (A : GPotG G) : Prop :=
  (∀ n : ℕ, ContDiff ℝ n A) ∧ ∀ x μ, GaugeLie.lieGen (G := G) (Matrix.of (A x μ))

/-- **The classical configuration** `ρ(U_μ(x)) = exp(i a g A_μ(a x))` at spacing `a`.

DERIVED: no numeral. -/
def IsClassCfgG (a g : ℝ) (A : GPotG G) (U : IConf G) : Prop :=
  ∀ l, GaugeGroup.repM G (U l)
    = NormedSpace.exp (Matrix.of ((Complex.I * ((a * g : ℝ) : ℂ)) • A (site a l.2) l.1))

/-- **The classical leading term** `(L(U) − L(1))/a^d → P(A, g)`.

DERIVED: `0` the point approached; `1` the unit configuration. -/
def ClassicalLeadG (L : IConf G → ℝ) (d : ℕ) (P : GPotG G → ℝ → ℝ) : Prop :=
  ∀ A : GPotG G, AdmPot A → ∀ (g : ℝ) (U : ℝ → IConf G), (∀ a, 0 < a → IsClassCfgG a g A (U a)) →
    Tendsto (fun a => (L (U a) - L (fun _ => (1 : G))) / a ^ d) (𝓝[>] (0 : ℝ))
      (𝓝 (P A g))

end Classical

/-! ## 2. The dimension-four sector -/

section Sector

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **Renormalisation with mixing** over `G`. DERIVED: no numeral. -/
structure RenormMixG (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [GaugeGroup G] where
  /-- The basis index. -/
  B : Type
  [fB : Fintype B]
  /-- The basis of lattice fields. -/
  op : B → LField G
  /-- The mixing matrix of step `k`. -/
  M : ℕ → Idx4 → B → ℝ

attribute [instance] RenormMixG.fB

/-- `RenormMix N` as a `RenormMixG (SU N)`. DERIVED: no numeral. -/
def _root_.MassGap.ClayStatement.RenormMix.toG {N : ℕ} [NeZero N] (ρ : RenormMix N) :
    RenormMixG (MassGap.SUN.SU N) :=
  ⟨ρ.B, ρ.op, ρ.M⟩

/-- `RenormMixG (SU N)` as a `RenormMix N`. DERIVED: no numeral. -/
def RenormMixG.toSU {N : ℕ} [NeZero N] (ρ : RenormMixG (MassGap.SUN.SU N)) : RenormMix N :=
  ⟨ρ.B, ρ.op, ρ.M⟩

/-- The Riemann-type symmetries of the mixing. DERIVED: no numeral. -/
def RenormMixG.Riemann (ρ : RenormMixG G) : Prop :=
  ∀ (k : ℕ) (α : Idx4) (b : ρ.B), ρ.M k (swap01 α) b = -ρ.M k α b
    ∧ ρ.M k (swap23 α) b = -ρ.M k α b ∧ ρ.M k (pairEx α) b = ρ.M k α b

/-- The coefficient of the basis field `b` in `∑_α c_α T_α`. DERIVED: no numeral. -/
def mixCG (ρ : RenormMixG G) (k : ℕ) (c : Idx4 → ℝ) (b : ρ.B) : ℝ := ∑ α, c α * ρ.M k α b

/-- The connected basis field with a test function. DERIVED: no numeral. -/
def locFieldG (S : Sched G) (ρ : RenormMixG G) (k : ℕ) (b : ρ.B) (f : TestFn) : SFieldG G :=
  ((ρ.op b).sub (S.ν k (ρ.op b).1), f)

/-- **The lattice Schwinger function of the sector at step `k`.** DERIVED: no numeral. -/
def latTG (S : Sched G) (ρ : RenormMixG G) (k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → TDatum) : ℝ :=
  ∑ b : ι → ρ.B, (∏ i, mixCG ρ k (F i).1 (b i)) * latSG S k (fun i => locFieldG S ρ k (b i) (F i).2)

/-- **The continuum Schwinger function of the sector**: the limit along `ultra`.

DERIVED: no numeral. -/
def contTG (S : Sched G) (ρ : RenormMixG G) {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → TDatum) : ℝ :=
  limUnder (ultra : Filter ℕ) (fun k => latTG S ρ k F)

/-- **The channel tie** over `G`. DERIVED: `4` the dimension; `2` the power of the coupling. -/
def ChannelTieG [GaugeSimple G] [GaugeLie G] (ρ : RenormMixG G) (Mb : Idx4 → ρ.B → ℝ)
    (Z : ℕ → Idx4 → Idx4 → ℝ) : Prop :=
  (∀ k α b, ρ.M k α b = ∑ β, Z k α β * Mb β b)
    ∧ (∀ k (A : Matrix (Fin 4) (Fin 4) ℝ), IsHyp A → ∀ c,
        zAct (Z k) (rotC A c) = rotC A (zAct (Z k) c))
    ∧ ∀ β, ClassicalLeadG (fun U => ∑ b, Mb β b * (ρ.op b).1 U) 4 (fun A g => g ^ 2 * ffT g A β)

/-- **The topological normalisation**: `zq k · a_k⁴ → K.cTop`. DERIVED: `4` the dimension. -/
def TopNormG (S : Sched G) (K : ClayConsts) (Z : ℕ → Idx4 → Idx4 → ℝ) : Prop :=
  ∃ zq : ℕ → ℝ, (∀ k, zAct (Z k) epsC = zq k • epsC)
    ∧ Tendsto (fun k => zq k * S.a k ^ 4) atTop (𝓝 K.cTop)

variable (S : Sched G) (ρ : RenormMixG G)

/-- **Existence of the limit** on every admissible family. DERIVED: no numeral. -/
def SepConvG : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → TDatum), Adm F →
    Tendsto (fun k => latTG S ρ k F) (ultra : Filter ℕ) (𝓝 (contTG S ρ F))

/-- **OS0, the kernel bound.** DERIVED: `1` the top of the separation; `0` its sign. -/
def OS0SepG : Prop :=
  ∃ α γ β κ : ℝ, ∀ (n : ℕ) (F : Fin n → TDatum) (d : ℝ), 0 < d → d ≤ 1 → ContD F → SepD d F →
    |contTG S ρ F| ≤ α * γ ^ n * (n.factorial : ℝ) ^ β * (d ^ (κ * n))⁻¹
      * ∏ i, (cnorm (F i).1 * l1 (F i).2)

/-- **OS1.** DERIVED: `4` the dimension. -/
def OS1SepG : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → TDatum), Adm F → ∀ v : Fin 4 → ℝ,
    Tendsto (fun k => latTG S ρ k (fun i => translateD v (F i))) (ultra : Filter ℕ)
      (𝓝 (contTG S ρ F))

/-- **`O(4)` covariance of the sector.** DERIVED: `4` the dimension. -/
def TensorCovG : Prop :=
  ∀ A : Matrix (Fin 4) (Fin 4) ℝ, A ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → TDatum), Adm F →
      Tendsto (fun k => latTG S ρ k (fun i => ((F i).1, rotTest A (F i).2))) (ultra : Filter ℕ)
        (𝓝 (contTG S ρ (fun i => (rotC A (F i).1, (F i).2))))

/-- **OS3**, as an identity of the lattice readings. DERIVED: no numeral. -/
def OS3TG : Prop :=
  ∀ (ι ι' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (e : ι' ≃ ι)
    (F : ι → TDatum) (k : ℕ), latTG S ρ k (F ∘ e) = latTG S ρ k F

/-- **The translation Ward identity.** DERIVED: `1` the differentiability order and the value of
`h`; `0` its other value and the sign of the separation. -/
def WardTG : Prop :=
  ∃ κ : ℝ, ∀ (ν : Fin 4) (n : ℕ) (F : Fin n → TDatum) (I : Finset (Fin n))
      (h : (Fin 4 → ℝ) → ℝ) (dh : Fin 4 → TestFn) (df : Fin n → TestFn) (d : ℝ),
    0 < d → Adm F → ContDiff ℝ 1 h → (∀ μ x, (dh μ).1 x = fderiv ℝ h x (dir μ)) →
    (∀ i, ContDiff ℝ 1 (F i).2.1) → (∀ i x, (df i).1 x = fderiv ℝ (F i).2.1 x (dir ν)) →
    (∀ i x y, (F i).2.1 x ≠ 0 → dist x y < d → h y = if i ∈ I then 1 else 0) →
    ∑ μ, contTG S ρ (Fin.cons (α := fun _ => TDatum) (stressC κ μ ν, dh μ) F)
      = -∑ i ∈ I, contTG S ρ (Function.update F i ((F i).1, df i))

/-- The local reading of `n` insertions of the trace. DERIVED: no numeral. -/
def contTrG {n : ℕ} (u : Fin n → TestFn) : ℝ := contTG S ρ (fun i => (trC, u i))

/-- **The two-point kernel of the trace.** DERIVED: `0` the sign of the separation and the end of
the half-line; `2` the order. -/
def TwoPointKernelG (Gk : ℝ → ℝ) : Prop :=
  ContinuousOn Gk (Set.Ioi 0)
    ∧ ∀ f g : TestFn, Continuous f.1 → Continuous g.1 → (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f g) →
      contTrG S ρ ![f, g] = ∫ x, ∫ y, f.1 x * g.1 y * Gk (ContinuumNontrivial.eDist x y)

/-- The connected three-point function of the trace. DERIVED: `1`, `2`, `3` the orders; `2` the
cumulant coefficient. -/
def cum3TG (f g h : TestFn) : ℝ :=
  contTrG S ρ ![f, g, h] - contTrG S ρ ![f, g] * contTrG S ρ ![h]
    - contTrG S ρ ![f, h] * contTrG S ρ ![g] - contTrG S ρ ![g, h] * contTrG S ρ ![f]
    + 2 * contTrG S ρ ![f] * contTrG S ρ ![g] * contTrG S ρ ![h]

/-- **Non-Gaussian.** DERIVED: `0` the Gaussian value and the sign of the separation. -/
def NonGaussianTG : Prop :=
  ∃ f g h : TestFn, Continuous f.1 ∧ Continuous g.1 ∧ Continuous h.1
    ∧ (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f g ∧ ContinuumSep.sepBy d f h
        ∧ ContinuumSep.sepBy d g h)
    ∧ cum3TG S ρ f g h ≠ 0

/-- **Every field of the sector is non-degenerate.** DERIVED: `0` the excluded values and the sign
of the separation; `2` the order. -/
def TensorNondegG : Prop :=
  ∀ c : Idx4 → ℝ, projR c ≠ 0 →
    ∃ f g : TestFn, Continuous f.1 ∧ Continuous g.1 ∧ (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f g)
      ∧ contTG S ρ ![(c, f), (c, g)] ≠ 0

end Sector

/-! ## 3. The aperture, the ties, the link -/

section Link

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The aperture's functional is a limit.** DERIVED: no numeral. -/
def ApertureConvG (S : Sched G) (W : ConfFlowG G) (D : Set (LField G)) : Prop :=
  UniformBoundFG S (energyMapG S W D)
    ∧ ∀ (ι : Type) [Fintype ι] (O : ι → LField G), (∀ i, O i ∈ D) →
      ∀ g : ι → Decaying,
        Tendsto (fun R : ℕ => contSFG S (energyMapG S W D) (fun i => (O i, cut (g i) R))) atTop
          (𝓝 (schwSFMG S W D O g))

/-- **The scalar tie**: the observer's field is `sym (plaqField q0)` of `G`, and the trace channel
is `Ztr k` times it with `Ztr k · a_k⁴ → K.cTr`.

DERIVED: `4` the dimension of the field. -/
def ScalarTieG (S : Sched G) (K : ClayConsts) (ρ : RenormMixG G) (O : LField G) : Prop :=
  O = symG (plaqFieldG ObserverEnergyMoments.q0)
    ∧ ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixCG ρ k trC b • (ρ.op b).1 = Ztr k • O.1)
      ∧ Tendsto (fun k => Ztr k * S.a k ^ 4) atTop (𝓝 K.cTr)

/-- **The asymptotic-freedom coefficient**: `r⁸ G(r) (log r)² → K.cAF`.

DERIVED: `8`, `2` as in `AFShortDistance`; `0` the point approached. -/
def AFCoefficientG (K : ClayConsts) (Gk : ℝ → ℝ) : Prop :=
  Tendsto (fun r => r ^ 8 * Gk r * Real.log r ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 K.cAF)

/-- **`AFCoefficientG` gives `AFShortDistance`** when `K.cAF > 0`. DERIVED: `0` the sign. -/
theorem afShortDistance_of_coefficientG {K : ClayConsts} (hK : 0 < K.cAF) {Gk : ℝ → ℝ}
    (h : AFCoefficientG K Gk) : ShortDistanceY.AFShortDistance Gk :=
  ⟨K.cAF, hK, h⟩

/-- **The reflection kernel** `S(ΘP ∪ Q)`. DERIVED: no numeral. -/
def kernTG (S : Sched G) (ρ : RenormMixG G) (τ : Fin 4) (P Q : TSep τ) : ℝ :=
  contTG S ρ (pairT τ P.1 Q.1)

/-- **The forward time step** by `a_m` in direction `τ`. DERIVED: `1` one step. -/
def shiftTG {Xd : Type} (S : Sched G) (τ : Fin 4) (m : ℕ) (P : TSepG Xd τ) : TSepG Xd τ :=
  ⟨⟨P.1.1, fun i => translateD (timeVecG S m τ 1) (P.1.2 i)⟩, by
    have hv : 0 ≤ timeVecG S m τ 1 τ := timeVecG_nonneg S m τ
    obtain ⟨hc, d, hd, h1, h2⟩ := P.2
    refine ⟨fun i => (hc i).comp (continuous_id.sub continuous_const), d, hd, fun i y hy => ?_,
      fun i j hij => ContinuumSep.sepBy_translate (h2 i j hij) _⟩
    have h := h1 i (y - timeVecG S m τ 1) hy
    have e : (y - timeVecG S m τ 1) τ = y τ - timeVecG S m τ 1 τ := rfl
    rw [e] at h
    linarith⟩

/-- **The mixed lattice reading** of step `k`: `ΘP` local, `Q` flowed by `Φ`.

DERIVED: no numeral. -/
def mixLatTG (S : Sched G) (ρ : RenormMixG G) (Φ : ℕ → LField G → LField G) (τ : Fin 4) (k : ℕ)
    (P : TMono) (Q : MonoG G) : ℝ :=
  ∑ b : Fin P.1 → ρ.B, (∏ i, mixCG ρ k (reflC τ (P.2 i).1) (b i))
    * latSG S k (Sum.elim (fun i => locFieldG S ρ k (b i) ((P.2 i).2.reflect τ))
        (fun j => (Φ k (Q.2 j).1, (Q.2 j).2)))

/-- The mixed reading: the limit along `ultra`. DERIVED: no numeral. -/
def mixTG (S : Sched G) (ρ : RenormMixG G) (Φ : ℕ → LField G → LField G) (τ : Fin 4) (P : TMono)
    (Q : MonoG G) : ℝ :=
  limUnder (ultra : Filter ℕ) (fun k => mixLatTG S ρ Φ τ k P Q)

variable {D : Set (LField G)} {τ : Fin 4} {r : ℝ}

/-- **The link of the sector to the aperture's Hilbert space.** DERIVED: `4` the dimension. -/
def LinkTSG (S : Sched G) (W : ConfFlowG G) (D : Set (LField G)) (X : OSDataSLinkedG G D τ r)
    (ρ : RenormMixG G) (w : TSep τ → X.base.H) : Prop :=
  (∀ P Q : TSep τ, Tendsto (fun k => latTG S ρ k (pairT τ P.1 Q.1)) (ultra : Filter ℕ)
        (𝓝 (kernTG S ρ τ P Q))
      ∧ inner ℂ (w P) (w Q) = (kernTG S ρ τ P Q : ℂ))
    ∧ (∀ (m : ℕ) (P : TSep τ), w (shiftTG S τ m P) = X.base.time (S.a m) (w P))
    ∧ w (emptyT τ) = X.base.vac
    ∧ ∀ (P : TSep τ) (Q : MarginMonoDG G D τ r),
        Tendsto (fun k => mixLatTG S ρ (energyMapG S W D) τ k P.1 Q.1.1) (ultra : Filter ℕ)
            (𝓝 (mixTG S ρ (energyMapG S W D) τ P.1 Q.1.1))
          ∧ inner ℂ (w P) (X.cvec Q) = (mixTG S ρ (energyMapG S W D) τ P.1 Q.1.1 : ℂ)

/-- **The reconstruction space of the sector.** DERIVED: no numeral. -/
def HLsG (X : OSDataSLinkedG G D τ r) (w : TSep τ → X.base.H) : Submodule ℂ X.base.H :=
  HLg X.base w

/-- **The observer carries the Hilbert space**: vectors `v P` of the compact margin monomials of
every local field that are the observer's compact vectors on the class `D`, with inner products the
observer's flowed Schwinger functions of the reflected pairs, `⟪v P, v Q⟫ = S_W(θP ∪ Q)`
(`contSFG` of `energyMapG S W D`), on which the time translation by `a_m` acts as the dyadic shift
of the test functions, and whose closed span is the whole space. `ClayStatement.ObsGen` over `G`.

DERIVED: `1` one step. -/
def ObsGenG (S : Sched G) (W : ConfFlowG G) (D : Set (LField G)) (X : OSDataSLinkedG G D τ r) :
    Prop :=
  ∃ v : MarginMonoG G τ r → X.base.H,
    (∀ Q : MarginMonoDG G D τ r, v Q.1 = X.cvec Q)
    ∧ (∀ P Q : MarginMonoG G τ r,
      inner ℂ (v P) (v Q) = (contSFG S (energyMapG S W D)
        (Sum.elim (fun i => ((P.1.2 i).1.refl τ, (P.1.2 i).2.reflect τ)) Q.1.2) : ℂ))
    ∧ (∀ (m : ℕ) (P Q : MarginMonoG G τ r),
      Q.1 = ⟨P.1.1, fun i => ((P.1.2 i).1, (P.1.2 i).2.translate (timeVecG S m τ 1))⟩ →
        v Q = X.base.time (S.a m) (v P))
    ∧ HLg X.base v = ⊤

/-- **OS2 at margin `0`.** DERIVED: `0` the sign. -/
def OS2TG (S : Sched G) (ρ : RenormMixG G) (τ : Fin 4) : Prop :=
  ∀ (s : Finset (TSep τ)) (c : TSep τ → ℝ), 0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * kernTG S ρ τ P Q

/-- **OS4, clustering.** DERIVED: no numeral. -/
def OS4TG (S : Sched G) (ρ : RenormMixG G) (τ : Fin 4) : Prop :=
  ∀ (m : ℕ) (P Q : TSep τ),
    Tendsto (fun n : ℕ => kernTG S ρ τ P ((shiftTG S τ m)^[n] Q)) atTop
      (𝓝 (kernTG S ρ τ P (emptyT τ) * kernTG S ρ τ (emptyT τ) Q))

end Link

/-! ## 4. All gauge-invariant local composites -/

section Comp

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **A family of local composites** over `G`. DERIVED: `4` the dimension. -/
structure CompositesG (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [GaugeGroup G] where
  /-- The index type. -/
  Ix : Type
  /-- The classical monomial. -/
  cl : Ix → CMono
  /-- The bare lattice field. -/
  bare : Ix → LField G
  /-- The renormalised lattice field of step `k`. -/
  ren : ℕ → Ix → LField G
  /-- The rotation representation. -/
  rep : Matrix (Fin 4) (Fin 4) ℝ → Ix → (Ix →₀ ℝ)

/-- `Composites N` as a `CompositesG (SU N)`. DERIVED: no numeral. -/
def _root_.MassGap.ClayStatement.Composites.toG {N : ℕ} [NeZero N] (C : Composites N) :
    CompositesG (MassGap.SUN.SU N) :=
  ⟨C.Ix, C.cl, C.bare, C.ren, C.rep⟩

/-- `CompositesG (SU N)` as a `Composites N`. DERIVED: no numeral. -/
def CompositesG.toSU {N : ℕ} [NeZero N] (C : CompositesG (MassGap.SUN.SU N)) : Composites N :=
  ⟨C.Ix, C.cl, C.bare, C.ren, C.rep⟩

/-- **Each bare field discretises its monomial.** DERIVED: no numeral. -/
def CompositesG.Tied [GaugeSimple G] [GaugeLie G] (C : CompositesG G) : Prop :=
  ∀ i, ClassicalLeadG (C.bare i).1 (cdim (C.cl i))
    (fun A g => g ^ cnF (C.cl i) * cval g A (C.cl i))

/-- **Every composite is in the family.** DERIVED: no numeral. -/
def CompositesG.Covers (C : CompositesG G) : Prop :=
  ∀ m : CMono, m ≠ [] → (∀ p ∈ m, p.1 ≠ []) → ∃ i, C.cl i = m

/-- The span of `1` and the fields `F i` of dimension `≤ d`. DERIVED: `1` the unit field. -/
def CompositesG.lowSpan (C : CompositesG G) (F : C.Ix → LField G) (d : ℕ) :
    Submodule ℝ (ContinuousMap (IConf G) ℝ) :=
  Submodule.span ℝ (insert 1 (Set.range fun i : {i // cdim (C.cl i) ≤ d} => (F i.1).1))

/-- **Triangular, invertible renormalisation.** DERIVED: no numeral. -/
def CompositesG.RenTri (C : CompositesG G) : Prop :=
  (∀ k i, (C.ren k i).1 ∈ C.lowSpan C.bare (cdim (C.cl i)))
    ∧ ∀ k d, C.lowSpan C.bare d ≤ C.lowSpan (C.ren k) d

/-- **The rotation representation is the classical one**, on every admissible potential
(`AdmPot`, the class `ClassicalLeadG` and `CompNondeg` read). DERIVED: `4` the dimension. -/
def CompositesG.RepTie [GaugeSimple G] [GaugeLie G] (C : CompositesG G) : Prop :=
  ∀ R : Matrix (Fin 4) (Fin 4) ℝ, R ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
    ∀ (i : C.Ix) (A : GPotG G), AdmPot A → ∀ g : ℝ,
      cval g (rotPot R A) (C.cl i) = ∑ j ∈ (C.rep R i).support, C.rep R i j * cval g A (C.cl j)

/-- **The composites clauses.** DERIVED: no numeral. -/
def CompDataG [GaugeSimple G] [GaugeLie G] (C : CompositesG G) : Prop :=
  C.Tied ∧ C.Covers ∧ C.RenTri ∧ C.RepTie

/-- A composite with a test function. DERIVED: no numeral. -/
abbrev CDatumG (C : CompositesG G) : Type := C.Ix × TestFn

/-- The connected renormalised composite with its test function. DERIVED: no numeral. -/
def cFieldG (S : Sched G) (C : CompositesG G) (k : ℕ) (p : CDatumG C) : SFieldG G :=
  ((C.ren k p.1).sub (S.ν k (C.ren k p.1).1), p.2)

/-- **The lattice Schwinger function of the composites at step `k`.** DERIVED: no numeral. -/
def latCG (S : Sched G) (C : CompositesG G) (k : ℕ) {ι : Type} [Fintype ι] (F : ι → CDatumG C) :
    ℝ :=
  latSG S k (fun i => cFieldG S C k (F i))

/-- **The continuum Schwinger function of the composites.** DERIVED: no numeral. -/
def contCG (S : Sched G) (C : CompositesG G) {ι : Type} [Fintype ι] (F : ι → CDatumG C) : ℝ :=
  limUnder (ultra : Filter ℕ) (fun k => latCG S C k F)

variable (S : Sched G) (C : CompositesG G)

/-- **Existence of the limit** on all composites. DERIVED: no numeral. -/
def ConvCG : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → CDatumG C), Adm F →
    Tendsto (fun k => latCG S C k F) (ultra : Filter ℕ) (𝓝 (contCG S C F))

/-- **OS0 on all composites.** DERIVED: `1` the top of the separation; `0` its sign. -/
def OS0CG : Prop :=
  ∃ (α γ β : ℝ) (Cc κ : C.Ix → ℝ), ∀ (n : ℕ) (F : Fin n → CDatumG C) (d : ℝ), 0 < d → d ≤ 1 →
    ContD F → SepD d F →
      |contCG S C F| ≤ α * γ ^ n * (n.factorial : ℝ) ^ β
        * ∏ i, (Cc (F i).1 * (d ^ κ (F i).1)⁻¹ * l1 (F i).2)

/-- **OS1 on all composites.** DERIVED: `4` the dimension. -/
def OS1CG : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → CDatumG C), Adm F → ∀ v : Fin 4 → ℝ,
    Tendsto (fun k => latCG S C k (fun i => translateD v (F i))) (ultra : Filter ℕ)
      (𝓝 (contCG S C F))

/-- **`O(4)` covariance of all composites.** DERIVED: `4` the dimension. -/
def CovCG : Prop :=
  ∀ R : Matrix (Fin 4) (Fin 4) ℝ, R ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → CDatumG C), Adm F →
      Tendsto (fun k => latCG S C k (fun i => ((F i).1, rotTest R (F i).2))) (ultra : Filter ℕ)
        (𝓝 (∑ σ ∈ Fintype.piFinset (fun i => (C.rep R (F i).1).support),
          (∏ i, C.rep R (F i).1 (σ i)) * contCG S C (fun i => (σ i, (F i).2))))

/-- **Non-degeneracy of all composites, modulo the equations of motion.**

DERIVED: `0` the excluded values and the sign of the separation; `2` the order. -/
def CompNondegG [GaugeSimple G] [GaugeLie G] : Prop :=
  ∀ c : C.Ix →₀ ℝ,
    (∃ (A : GPotG G) (g : ℝ), AdmPot A ∧ OnShell g A
      ∧ ∑ i ∈ c.support.filter (fun i => cdim (C.cl i) = c.support.sup (fun j => cdim (C.cl j))),
          c i * g ^ cnF (C.cl i) * cval g A (C.cl i) ≠ 0) →
    ∃ f h : TestFn, Continuous f.1 ∧ Continuous h.1 ∧ (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f h)
      ∧ ∑ i ∈ c.support, ∑ j ∈ c.support,
          c i * c j * contCG S C (![(i, f), (j, h)] : Fin 2 → CDatumG C) ≠ 0

/-- **The analytic clauses on all composites.** DERIVED: no numeral. -/
def CompOSG [GaugeSimple G] [GaugeLie G] : Prop :=
  ConvCG S C ∧ OS0CG S C ∧ OS1CG S C ∧ CovCG S C ∧ CompNondegG S C

/-- **OS3 on all composites.** DERIVED: no numeral. -/
def OS3CG : Prop :=
  ∀ (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι' ≃ ι) (F : ι → CDatumG C) (k : ℕ),
    latCG S C k (F ∘ e) = latCG S C k F

/-- The reflection sign of a monomial of composites. DERIVED: `1` the sign. -/
def sgnCG (τ : Fin 4) (P : TMonoG C.Ix) : ℝ := ∏ i, (-1 : ℝ) ^ ctau τ (C.cl (P.2 i).1)

/-- `ΘP ∪ Q` for composites. DERIVED: `4` the dimension. -/
def pairCG (τ : Fin 4) (P Q : TMonoG C.Ix) : Fin P.1 ⊕ Fin Q.1 → CDatumG C :=
  Sum.elim (fun i => ((P.2 i).1, (P.2 i).2.reflect τ)) Q.2

/-- **The reflection kernel of the composites** `sgn(P) S(ΘP ∪ Q)`. DERIVED: no numeral. -/
def kernCG (τ : Fin 4) (P Q : TSepG C.Ix τ) : ℝ :=
  sgnCG C τ P.1 * contCG S C (pairCG C τ P.1 Q.1)

/-- **OS2 on all composites.** DERIVED: `0` the sign. -/
def OS2CG (τ : Fin 4) : Prop :=
  ∀ (s : Finset (TSepG C.Ix τ)) (c : TSepG C.Ix τ → ℝ),
    0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * kernCG S C τ P Q

/-- **OS4 on all composites.** DERIVED: no numeral. -/
def OS4CG (τ : Fin 4) : Prop :=
  ∀ (m : ℕ) (P Q : TSepG C.Ix τ),
    Tendsto (fun n : ℕ => kernCG S C τ P ((shiftTG S τ m)^[n] Q)) atTop
      (𝓝 (kernCG S C τ P (emptyG C.Ix τ) * kernCG S C τ (emptyG C.Ix τ) Q))

end Comp

section LinkC

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {D : Set (LField G)} {τ : Fin 4} {r : ℝ}

/-- **The link of all composites.** DERIVED: no numeral. -/
def LinkCG (S : Sched G) (X : OSDataSLinkedG G D τ r) (C : CompositesG G)
    (wC : TSepG C.Ix τ → X.base.H) : Prop :=
  (∀ P Q : TSepG C.Ix τ,
      Tendsto (fun k => latCG S C k (pairCG C τ P.1 Q.1)) (ultra : Filter ℕ)
          (𝓝 (contCG S C (pairCG C τ P.1 Q.1)))
        ∧ inner ℂ (wC P) (wC Q) = (kernCG S C τ P Q : ℂ))
    ∧ (∀ (m : ℕ) (P : TSepG C.Ix τ), wC (shiftTG S τ m P) = X.base.time (S.a m) (wC P))
    ∧ wC (emptyG C.Ix τ) = X.base.vac

/-- **The Hilbert space of all local fields.** DERIVED: no numeral. -/
def HLCG (X : OSDataSLinkedG G D τ r) {C : CompositesG G} (wC : TSepG C.Ix τ → X.base.H) :
    Submodule ℂ X.base.H :=
  HLg X.base wC

/-- **The tensor among the composites.** DERIVED: `0`–`3` the slots. -/
def TInG (ρ : RenormMixG G) (C : CompositesG G) (X : OSDataSLinkedG G D τ r)
    (w : TSep τ → X.base.H) (wC : TSepG C.Ix τ → X.base.H) : Prop :=
  ∃ e : Idx4 → C.Ix, (∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    ∧ (∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    ∧ HLsG X w ≤ HLCG X wC

end LinkC

/-! ## 5. The statement -/

section Statement

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G] [GaugeLie G]

/-- **All clauses at one witness**, at the schedule `S` and constants `K`; the list of
`ClayStatement.ClayData`, in the same order.

DERIVED: `0` the vanishing pairing and the zero vector; `4` the dimension. -/
def ClayDataP (S : Sched G) (K : ClayConsts) (W : ConfFlowG G) (D : Set (LField G)) (τ : Fin 4)
    (r : ℝ) (X : OSDataSLinkedG G D τ r) (ρ : RenormMixG G) (Gk : ℝ → ℝ) (w : TSep τ → X.base.H)
    (C : CompositesG G) (wC : TSepG C.Ix τ → X.base.H) : Prop :=
  (∀ (ι : Type) [Fintype ι] (O : ι → LField G) (g : ι → Decaying),
      X.SM O g = schwSFMG S W D O g)
    ∧ HamiltonianGap X.base
    ∧ ρ.Riemann ∧ ScalarTieG S K ρ X.O
    ∧ SepConvG S ρ ∧ OS0SepG S ρ
    ∧ OS1SepG S ρ ∧ TensorCovG S ρ
    ∧ OS3TG S ρ
    ∧ LinkTSG S W D X ρ w ∧ OS2TG S ρ τ
    ∧ SpectralGapOn X.base (HLsG X w) ∧ OS4TG S ρ τ
    ∧ (∃ u ∈ HLsG X w, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    ∧ TwoPointKernelG S ρ Gk ∧ AFCoefficientG K Gk
    ∧ ShortDistanceY.AFShortDistance Gk
    ∧ NonGaussianTG S ρ
    ∧ TensorNondegG S ρ
    ∧ ApertureConvG S W D
    ∧ (∃ (Mb : Idx4 → ρ.B → ℝ) (Z : ℕ → Idx4 → Idx4 → ℝ), ChannelTieG ρ Mb Z ∧ TopNormG S K Z)
    ∧ WardTG S ρ
    ∧ CompDataG C ∧ CompOSG S C ∧ OS3CG S C
    ∧ LinkCG S X C wC ∧ OS2CG S C τ
    ∧ OS4CG S C τ
    ∧ TInG ρ C X w wC
    ∧ SpectralGapOn X.base (HLCG X wC)
    ∧ (∃ u ∈ HLCG X wC, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    ∧ ObsGenG S W D X

/-- **The Clay statement at one configuration flow, schedule and constants.**

DERIVED: `4` the dimension. -/
def ClayStatementAtP (S : Sched G) (K : ClayConsts) (W : ConfFlowG G) (D : Set (LField G)) :
    Prop :=
  ∃ (τ : Fin 4) (r : ℝ) (X : OSDataSLinkedG G D τ r) (ρ : RenormMixG G) (Gk : ℝ → ℝ)
    (w : TSep τ → X.base.H) (C : CompositesG G) (wC : TSepG C.Ix τ → X.base.H),
    ClayDataP S K W D τ r X ρ Gk w C wC

variable (G)

/-- **The Clay statement for `G` at one configuration flow**: the canonical schedule and the
constants of `G`.

DERIVED: no numeral. -/
def ClayStatementAtG (W : ConfFlowG G) (D : Set (LField G)) : Prop :=
  ClayStatementAtP (canonSched G) (constsG G) W D

/-- **The Clay Yang–Mills statement for `G` at the frozen tower**: some configuration flow and some
reflection-closed class of fields at which `ClayStatementAtG` holds.

DERIVED: `4` the dimension. -/
def ClayStatementOfDy : Prop :=
  ∃ (W : ConfFlowG G) (D : Set (LField G)),
    (∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D) ∧ ClayStatementAtG G W D

/-- **The Clay Yang–Mills statement for `G`**: some measured tower `βs`, configuration flow and
reflection-closed class of fields at which every clause of `ClayStatementAtP` holds at the schedule
along `βs`, with the constants of `G`.

DERIVED: `4` the dimension. -/
def ClayStatementOf : Prop :=
  ∃ βs : ℕ → ℝ, MeasTowerG G βs ∧
    ∃ (W : ConfFlowG G) (D : Set (LField G)),
      (∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D) ∧
      ClayStatementAtP (schedAlongG G βs) (constsG G) W D

end Statement

/-! ## 6. The specialisation to `SU(N)` -/

section Specialise

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

set_option maxRecDepth 100000 in
/-- **At `SU(N)`, every clause at one witness is the `SU(N)` clause**: `ClayDataP` at
`ClayStatement`'s schedule and constants, at the witnesses passed to `G`, is `ClayData`, by
definition.

DERIVED: `2` the least colour count; `4` the dimension. -/
theorem clayDataP_SU_iff (hN2 : 2 ≤ N) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) (τ : Fin 4)
    (r : ℝ) (X : OSDataSLinked N D τ r) (ρ : RenormMix N) (Gk : ℝ → ℝ) (w : TSep τ → X.base.H)
    (C : Composites N) (wC : TSepG C.Ix τ → X.base.H) :
    ClayDataP (schedSU N) (constsSU N) W.toG D τ r X.toG ρ.toG Gk w C.toG wC
      ↔ ClayData hN2 W D hD τ r X ρ Gk w C wC :=
  Iff.rfl

#print axioms clayDataP_SU_iff

set_option maxRecDepth 100000 in
/-- **At `SU(N)`, the parametric statement at `ClayStatement`'s schedule and constants is
`ClayStatementAt`.** Each witness passes field by field, and each clause is the `SU(N)` clause by
definition.

DERIVED: `2` the least colour count; `4` the dimension. -/
theorem clayStatementAtP_SU_iff (hN2 : 2 ≤ N) (W : ConfFlow N)
    (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) :
    ClayStatementAtP (schedSU N) (constsSU N) W.toG D ↔ ClayStatementAt hN2 W D hD := by
  constructor
  · rintro ⟨τ, r, X, ρ, Gk, w, C, wC, h⟩
    exact ⟨τ, r, X.toSU, ρ.toSU, Gk, w, C.toSU, wC,
      (clayDataP_SU_iff hN2 W D hD τ r X.toSU ρ.toSU Gk w C.toSU wC).1 h, trivial⟩
  · rintro ⟨τ, r, X, ρ, Gk, w, C, wC, h, -⟩
    exact ⟨τ, r, X.toG, ρ.toG, Gk, w, C.toG, wC,
      (clayDataP_SU_iff hN2 W D hD τ r X ρ Gk w C wC).2 h⟩

#print axioms clayStatementAtP_SU_iff

/-- **At `SU(N)`, `N ≥ 2`, `ClayStatementAtG` is `ClayStatementAt`.**

DERIVED: `2` the least colour count; `4` the dimension. -/
theorem clayStatementAtG_SU_iff (hN2 : 2 ≤ N) (W : ConfFlow N)
    (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) :
    ClayStatementAtG (MassGap.SUN.SU N) W.toG D ↔ ClayStatementAt hN2 W D hD := by
  unfold ClayStatementAtG
  rw [canonSched_SU N, constsG_SU N]
  exact clayStatementAtP_SU_iff hN2 W D hD

#print axioms clayStatementAtG_SU_iff

/-- **`ClayStatementOfDy (SU N)` is the `N` instance of `ClayStatementDy`.**

DERIVED: `2` the least colour count; `4` the dimension. -/
theorem clayStatementOfDy_SU_iff (hN2 : 2 ≤ N) :
    ClayStatementOfDy (MassGap.SUN.SU N) ↔
      ∃ (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
        (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D),
        ClayStatementAt hN2 W D hD := by
  constructor
  · rintro ⟨W, D, hD, h⟩
    exact ⟨W.toSU, D, hD, (clayStatementAtG_SU_iff hN2 W.toSU D hD).1 h⟩
  · rintro ⟨W, D, hD, h⟩
    exact ⟨W.toG, D, hD, (clayStatementAtG_SU_iff hN2 W D hD).2 h⟩

#print axioms clayStatementOfDy_SU_iff

end Specialise

/-- **`ClayStatementOf` at `SU(N)`**, with the instances `NeZero N`, `Fact (2 ≤ N)` from `N ≥ 2`.

DERIVED: `2` the least colour count; `0` the excluded one. -/
def ClayStatementSU (N : ℕ) (hN2 : 2 ≤ N) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  haveI : Fact (2 ≤ N) := ⟨hN2⟩
  ClayStatementOf (MassGap.SUN.SU N)

/-- **`ClayStatementOfDy` at `SU(N)`**, with the instances `NeZero N`, `Fact (2 ≤ N)` from `N ≥ 2`.

DERIVED: `2` the least colour count; `0` the excluded one. -/
def ClayStatementSUDy (N : ℕ) (hN2 : 2 ≤ N) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  haveI : Fact (2 ≤ N) := ⟨hN2⟩
  ClayStatementOfDy (MassGap.SUN.SU N)

/-- DERIVED: `2` the least colour count; `0` the excluded one. -/
theorem clayStatementSUDy_iff (N : ℕ) (hN2 : 2 ≤ N) :
    ClayStatementSUDy N hN2 ↔
      ∃ (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
        (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D),
        ClayStatementAt hN2 W D hD := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : Fact (2 ≤ N) := ⟨hN2⟩
  exact clayStatementOfDy_SU_iff hN2

#print axioms clayStatementSUDy_iff

/-- **`ClayStatementDy` is `ClayStatementOfDy` at every `SU(N)`, `N ≥ 2`.**

DERIVED: `2` the least colour count. -/
theorem clayStatementDy_iff_SU :
    MassGap.ClayStatementDy ↔ ∀ (N : ℕ) (hN2 : 2 ≤ N), ClayStatementSUDy N hN2 :=
  ⟨fun h N hN2 => (clayStatementSUDy_iff N hN2).2 (h N hN2),
    fun h N hN2 => (clayStatementSUDy_iff N hN2).1 (h N hN2)⟩

#print axioms clayStatementDy_iff_SU

/-- **The Clay Yang–Mills statement**: `ClayStatementOf` at every `SU(N)`, `N ≥ 2`.

DERIVED: `2` the least colour count. -/
def _root_.MassGap.ClayStatement : Prop := ∀ (N : ℕ) (hN2 : 2 ≤ N), ClayStatementSU N hN2

/-- DERIVED: `2` the least colour count. -/
theorem clayStatement_iff_SU :
    MassGap.ClayStatement ↔ ∀ (N : ℕ) (hN2 : 2 ≤ N), ClayStatementSU N hN2 :=
  Iff.rfl

#print axioms clayStatement_iff_SU

/-! ## 7. The statement over the instantiated groups -/

/-- `ClayStatementOf` at `SO(n)`, `n ≥ 5`. DERIVED: `5` the least `n`; `0` the excluded one. -/
def ClayStatementSO (n : ℕ) (h5 : 5 ≤ n) : Prop :=
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (5 ≤ n) := ⟨h5⟩
  ClayStatementOf (MassGap.GaugeInstances.SO n)

/-- `ClayStatementOf` at compact `Sp(n)`, `n ≥ 1`. DERIVED: `0` the excluded rank. -/
def ClayStatementUSp (n : ℕ) (hn : n ≠ 0) : Prop :=
  haveI : NeZero n := ⟨hn⟩
  ClayStatementOf (MassGap.GaugeInstances.USp n)

/-- **The Clay statement at every compact simple group instantiated in the tree**: `SU(N)`,
`N ≥ 2`; `SO(n)`, `n ≥ 5`; `SO(3)`; compact `Sp(n)`, `n ≥ 1`.

DERIVED: `2`, `5`, `3`, `0` the ranges of the families. -/
def ClayStatementClassical : Prop :=
  (∀ (N : ℕ) (hN2 : 2 ≤ N), ClayStatementSU N hN2)
    ∧ (∀ (n : ℕ) (h5 : 5 ≤ n), ClayStatementSO n h5)
    ∧ ClayStatementOf (MassGap.GaugeInstances.SO 3)
    ∧ ∀ (n : ℕ) (hn : n ≠ 0), ClayStatementUSp n hn

/-- **The statement over the instantiated groups implies `ClayStatement`.** DERIVED: no numeral. -/
theorem clayStatement_of_classical (h : ClayStatementClassical) : MassGap.ClayStatement :=
  h.1

#print axioms clayStatement_of_classical

/-- `ClayStatementOfDy` at `SO(n)`, `n ≥ 5`. DERIVED: `5` the least `n`; `0` the excluded one. -/
def ClayStatementSODy (n : ℕ) (h5 : 5 ≤ n) : Prop :=
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (5 ≤ n) := ⟨h5⟩
  ClayStatementOfDy (MassGap.GaugeInstances.SO n)

/-- `ClayStatementOfDy` at compact `Sp(n)`, `n ≥ 1`. DERIVED: `0` the excluded rank. -/
def ClayStatementUSpDy (n : ℕ) (hn : n ≠ 0) : Prop :=
  haveI : NeZero n := ⟨hn⟩
  ClayStatementOfDy (MassGap.GaugeInstances.USp n)

/-- **The statement over the instantiated groups at the frozen tower**: `ClayStatementOfDy` at the
groups of `ClayStatementClassical`.

DERIVED: `2`, `5`, `3`, `0` the ranges of the families. -/
def ClayStatementClassicalDy : Prop :=
  (∀ (N : ℕ) (hN2 : 2 ≤ N), ClayStatementSUDy N hN2)
    ∧ (∀ (n : ℕ) (h5 : 5 ≤ n), ClayStatementSODy n h5)
    ∧ ClayStatementOfDy (MassGap.GaugeInstances.SO 3)
    ∧ ∀ (n : ℕ) (hn : n ≠ 0), ClayStatementUSpDy n hn

/-- **At the frozen tower, the statement over the instantiated groups implies `ClayStatementDy`.**
DERIVED: no numeral. -/
theorem clayStatementDy_of_classicalDy (h : ClayStatementClassicalDy) : MassGap.ClayStatementDy :=
  clayStatementDy_iff_SU.2 h.1

#print axioms clayStatementDy_of_classicalDy

/-! ## 8. What transfers, over `G` -/

section Transfer

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **OS3 at every step.** DERIVED: no numeral. -/
theorem os3TG (S : Sched G) (ρ : RenormMixG G) : OS3TG S ρ := by
  intro ι ι' _ _ _ _ e F k
  unfold latTG
  refine Fintype.sum_equiv (e.arrowCongr (Equiv.refl ρ.B)) _ _ (fun b => ?_)
  have hb : ∀ i', (e.arrowCongr (Equiv.refl ρ.B) b) (e i') = b i' := fun i' => by
    simp [Equiv.arrowCongr_apply]
  congr 1
  · rw [← Equiv.prod_comp e]
    exact Finset.prod_congr rfl (fun i' _ => by rw [hb]; rfl)
  · have hG : (fun i' => locFieldG S ρ k (b i') ((F ∘ e) i').2)
        = (fun i => locFieldG S ρ k ((e.arrowCongr (Equiv.refl ρ.B)) b i) (F i).2) ∘ e := by
      funext i'
      simp only [Function.comp_apply, hb]
    rw [hG]
    exact latSG_comp_equiv S k e _

#print axioms os3TG

/-- **OS3 on all composites.** DERIVED: no numeral. -/
theorem os3CG (S : Sched G) (C : CompositesG G) : OS3CG S C := by
  intro ι ι' _ _ e F k
  exact latSG_comp_equiv S k e (fun i => cFieldG S C k (F i))

#print axioms os3CG

/-- The lattice reading of a family over an empty type is `1`. DERIVED: `1` the value. -/
theorem latTG_of_isEmpty (S : Sched G) (ρ : RenormMixG G) (k : ℕ) {ι : Type} [Fintype ι]
    [DecidableEq ι] [IsEmpty ι] (F : ι → TDatum) : latTG S ρ k F = 1 := by
  unfold latTG
  rw [Fintype.sum_unique, Fintype.prod_empty, one_mul]
  show (S.ν k) (∏ i, smear (S.a k) _ _) = 1
  rw [Fintype.prod_empty]
  exact (S.ν k).map_one

/-- The lattice reading of composites over an empty type is `1`. DERIVED: `1` the value. -/
theorem latCG_of_isEmpty (S : Sched G) (C : CompositesG G) (k : ℕ) {ι : Type} [Fintype ι]
    [IsEmpty ι] (F : ι → CDatumG C) : latCG S C k F = 1 := by
  show (S.ν k) (∏ i, smear (S.a k) _ _) = 1
  rw [Fintype.prod_empty]
  exact (S.ν k).map_one

/-- **`S(Θ∅ ∪ ∅) = 1`.** DERIVED: `1` the value. -/
theorem kernTG_empty (S : Sched G) (ρ : RenormMixG G) (τ : Fin 4) :
    kernTG S ρ τ (emptyT τ) (emptyT τ) = 1 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  haveI : IsEmpty (Fin (emptyT τ).1.1 ⊕ Fin (emptyT τ).1.1) := by
    show IsEmpty (Fin 0 ⊕ Fin 0)
    infer_instance
  unfold kernTG contTG
  have e : (fun k => latTG S ρ k (pairT τ (emptyT τ).1 (emptyT τ).1)) = fun _ => (1 : ℝ) :=
    funext fun k => latTG_of_isEmpty S ρ k _
  rw [e]
  exact tendsto_const_nhds.limUnder_eq

#print axioms kernTG_empty

/-- **`sgn(∅) S(Θ∅ ∪ ∅) = 1`** for the composites. DERIVED: `1` the value. -/
theorem kernCG_empty (S : Sched G) (C : CompositesG G) (τ : Fin 4) :
    kernCG S C τ (emptyG C.Ix τ) (emptyG C.Ix τ) = 1 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  haveI : IsEmpty (Fin (emptyG C.Ix τ).1.1 ⊕ Fin (emptyG C.Ix τ).1.1) := by
    show IsEmpty (Fin 0 ⊕ Fin 0)
    infer_instance
  haveI : IsEmpty (Fin (emptyG C.Ix τ).1.1) := by
    show IsEmpty (Fin 0)
    infer_instance
  unfold kernCG contCG sgnCG
  have e : (fun k => latCG S C k (pairCG C τ (emptyG C.Ix τ).1 (emptyG C.Ix τ).1))
      = fun _ => (1 : ℝ) :=
    funext fun k => latCG_of_isEmpty S C k _
  have h1 : limUnder (ultra : Filter ℕ) (fun _ : ℕ => (1 : ℝ)) = 1 :=
    tendsto_const_nhds.limUnder_eq
  rw [e, h1, Fintype.prod_empty, one_mul]

#print axioms kernCG_empty

/-- **The closed span is invariant under every `t ≥ 0`** when the shifts by the spacings of a
schedule keep the family.

DERIVED: `0` the time origin and signs. -/
theorem time_mem_HLgS (S : Sched G) (Y : OSDataS) {M : Type} (w : M → Y.H) (sh : ℕ → M → M)
    (hsh : ∀ (m : ℕ) (P : M), w (sh m P) = Y.time (S.a m) (w P))
    (t : ℝ) (ht : 0 ≤ t) : ∀ u ∈ HLg Y w, Y.time t u ∈ HLg Y w := by
  intro u hu
  set a : ℕ → ℝ := S.a with ha_def
  have ha : ∀ k, 0 < a k := S.a_pos
  set s : ℕ → ℝ := fun k => (⌊t / a k⌋₊ : ℝ) * a k with hs_def
  have hsle : ∀ k, s k ≤ t := fun k => by
    have h1 := Nat.floor_le (div_nonneg ht (ha k).le)
    exact (le_div_iff₀ (ha k)).mp h1
  have hsge : ∀ k, t - a k ≤ s k := fun k => by
    have h1 := Nat.lt_floor_add_one (t / a k)
    have h2 : t < ((⌊t / a k⌋₊ : ℝ) + 1) * a k := (div_lt_iff₀ (ha k)).mp h1
    show t - a k ≤ (⌊t / a k⌋₊ : ℝ) * a k
    nlinarith
  have hs0 : ∀ k, 0 ≤ s k := fun k => mul_nonneg (Nat.cast_nonneg _) (ha k).le
  have hlim : Tendsto s atTop (𝓝 t) := by
    have hlow : Tendsto (fun k => t - a k) atTop (𝓝 t) := by
      have := (tendsto_const_nhds (x := t)).sub S.a_lim
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hsge hsle
  have hlimW : Tendsto s atTop (𝓝[Set.Ici 0] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall hs0⟩
  have hcont : Tendsto (fun k => Y.time (s k) u) atTop (𝓝 (Y.time t u)) :=
    ((Y.time_cont u) t ht).tendsto.comp hlimW
  have hmem : ∀ k, Y.time (s k) u ∈ HLg Y w := fun k => by
    rw [hs_def, ← iterate_time Y (ha k).le]
    induction ⌊t / a k⌋₊ with
    | zero => exact hu
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact dyadic_mem_HLg Y w (a k) (sh k) (hsh k) _ ih
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hcont
    (Filter.Eventually.of_forall hmem)

#print axioms time_mem_HLgS

/-- **The spectral clause on the closed span** of any family the shifts keep, containing the
vacuum, from the Hamiltonian gap. DERIVED: no numeral. -/
theorem spectralGapOn_of_shiftS (S : Sched G) (Y : OSDataS) {M : Type} (w : M → Y.H)
    (hH : HamiltonianGap Y) (sh : ℕ → M → M)
    (hsh : ∀ (m : ℕ) (P : M), w (sh m P) = Y.time (S.a m) (w P)) (e : M)
    (hvac : w e = Y.vac) : SpectralGapOn Y (HLg Y w) :=
  ⟨hH.1, fun t ht => time_mem_HLgS S Y w sh hsh t ht,
    hvac ▸ Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_, rfl⟩),
    hH.2.2.1, fun u _ hu => hH.2.2.2.1 u hu, fun u _ hu t ht => Y.time_gap t ht u hu,
    fun t ht u _ hu => hH.2.2.2.2 t ht u hu⟩

#print axioms spectralGapOn_of_shiftS

variable {D : Set (LField G)} {τ : Fin 4} {r : ℝ}

/-- **What transfers, at one witness, over `G`.** The proved clauses and the open inputs are those
of `ClayStatement.clayData_of_link`, stated on the `G` objects at the schedule `S` and constants
`K`, with `0 < K.cAF`.

DERIVED: `0` the vanishing pairing, the zero vector and the sign of `K.cAF`. -/
theorem clayDataP_of_link [GaugeSimple G] [GaugeLie G] (S : Sched G) (K : ClayConsts)
    (hKpos : 0 < K.cAF) (W : ConfFlowG G) (D : Set (LField G))
    (X : OSDataSLinkedG G D τ r) (ρ : RenormMixG G) (Gk : ℝ → ℝ) (w : TSep τ → X.base.H)
    (hSM : ∀ (ι : Type) [Fintype ι] (O : ι → LField G) (g : ι → Decaying),
      X.SM O g = schwSFMG S W D O g)
    (hH : HamiltonianGap X.base) (hRie : ρ.Riemann) (hTie : ScalarTieG S K ρ X.O)
    (hConv : SepConvG S ρ) (h0 : OS0SepG S ρ) (h1 : OS1SepG S ρ) (hCov : TensorCovG S ρ)
    (hL : LinkTSG S W D X ρ w)
    (hnt : ∃ u ∈ HLsG X w, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    (hK : TwoPointKernelG S ρ Gk) (hAF : AFCoefficientG K Gk)
    (hNG : NonGaussianTG S ρ) (hND : TensorNondegG S ρ) (hAC : ApertureConvG S W D)
    (C : CompositesG G) (wC : TSepG C.Ix τ → X.base.H)
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Z : ℕ → Idx4 → Idx4 → ℝ), ChannelTieG ρ Mb Z ∧ TopNormG S K Z)
    (hWard : WardTG S ρ) (hCD : CompDataG C) (hCO : CompOSG S C) (hLC : LinkCG S X C wC)
    (hTI : TInG ρ C X w wC) (hGen : ObsGenG S W D X) : ClayDataP S K W D τ r X ρ Gk w C wC :=
  have hin : ∀ P Q : TSep τ, inner ℂ (w P) (w Q) = (kernTG S ρ τ P Q : ℂ) :=
    fun P Q => (hL.1 P Q).2
  have hinC : ∀ P Q : TSepG C.Ix τ, inner ℂ (wC P) (wC Q) = (kernCG S C τ P Q : ℂ) :=
    fun P Q => (hLC.1 P Q).2
  ⟨hSM, hH, hRie, hTie, hConv, h0, h1, hCov, os3TG S ρ, hL,
    fun s c => gram_nonneg X.base w (kernTG S ρ τ) hin s c,
    spectralGapOn_of_shiftS S X.base w hH (shiftTG S τ) hL.2.1 (emptyT τ) hL.2.2.1,
    fun m P Q => cluster_of_gram X.base w (kernTG S ρ τ) hin (shiftTG S τ m) (S.a_pos m)
      (hL.2.1 m) (emptyT τ) hL.2.2.1 (kernTG_empty S ρ τ) P Q,
    hnt, hK, hAF, afShortDistance_of_coefficientG hKpos hAF, hNG, hND, hAC, hCT, hWard, hCD, hCO,
    os3CG S C, hLC,
    fun s c => gram_nonneg X.base wC (kernCG S C τ) hinC s c,
    fun m P Q => cluster_of_gram X.base wC (kernCG S C τ) hinC (shiftTG S τ m) (S.a_pos m)
      (hLC.2.1 m) (emptyG C.Ix τ) hLC.2.2 (kernCG_empty S C τ) P Q,
    hTI,
    spectralGapOn_of_shiftS S X.base wC hH (shiftTG S τ) hLC.2.1 (emptyG C.Ix τ) hLC.2.2,
    by
      obtain ⟨_, _, _, hle⟩ := hTI
      obtain ⟨u, hu, h0', hne⟩ := hnt
      exact ⟨u, hle hu, h0', hne⟩,
    hGen⟩

#print axioms clayDataP_of_link

/-- **`ClayStatementAtP` from the inputs of `clayDataP_of_link`.**

DERIVED: `0` the sign of `K.cAF`. -/
theorem clayStatementAtP_of_link [GaugeSimple G] [GaugeLie G] (S : Sched G) (K : ClayConsts)
    (hKpos : 0 < K.cAF) (W : ConfFlowG G) (D : Set (LField G))
    (X : OSDataSLinkedG G D τ r) (ρ : RenormMixG G) (Gk : ℝ → ℝ) (w : TSep τ → X.base.H)
    (hSM : ∀ (ι : Type) [Fintype ι] (O : ι → LField G) (g : ι → Decaying),
      X.SM O g = schwSFMG S W D O g)
    (hH : HamiltonianGap X.base) (hRie : ρ.Riemann) (hTie : ScalarTieG S K ρ X.O)
    (hConv : SepConvG S ρ) (h0 : OS0SepG S ρ) (h1 : OS1SepG S ρ) (hCov : TensorCovG S ρ)
    (hL : LinkTSG S W D X ρ w)
    (hnt : ∃ u ∈ HLsG X w, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    (hK : TwoPointKernelG S ρ Gk) (hAF : AFCoefficientG K Gk)
    (hNG : NonGaussianTG S ρ) (hND : TensorNondegG S ρ) (hAC : ApertureConvG S W D)
    (C : CompositesG G) (wC : TSepG C.Ix τ → X.base.H)
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Z : ℕ → Idx4 → Idx4 → ℝ), ChannelTieG ρ Mb Z ∧ TopNormG S K Z)
    (hWard : WardTG S ρ) (hCD : CompDataG C) (hCO : CompOSG S C) (hLC : LinkCG S X C wC)
    (hTI : TInG ρ C X w wC) (hGen : ObsGenG S W D X) : ClayStatementAtP S K W D :=
  ⟨τ, r, X, ρ, Gk, w, C, wC,
    clayDataP_of_link S K hKpos W D X ρ Gk w hSM hH hRie hTie hConv h0 h1 hCov hL hnt hK hAF hNG
      hND hAC C wC hCT hWard hCD hCO hLC hTI hGen⟩

#print axioms clayStatementAtP_of_link

/-- **The `G` capstone**: `ClayStatementAtG G W D` from the inputs of `clayDataP_of_link` at the
canonical schedule and the constants of `G`.

DERIVED: no numeral. -/
theorem clayStatementAtG_of_link [GaugeSimple G] [GaugeLie G] (W : ConfFlowG G)
    (D : Set (LField G)) (X : OSDataSLinkedG G D τ r) (ρ : RenormMixG G) (Gk : ℝ → ℝ)
    (w : TSep τ → X.base.H)
    (hSM : ∀ (ι : Type) [Fintype ι] (O : ι → LField G) (g : ι → Decaying),
      X.SM O g = schwSFMG (canonSched G) W D O g)
    (hH : HamiltonianGap X.base) (hRie : ρ.Riemann)
    (hTie : ScalarTieG (canonSched G) (constsG G) ρ X.O)
    (hConv : SepConvG (canonSched G) ρ) (h0 : OS0SepG (canonSched G) ρ)
    (h1 : OS1SepG (canonSched G) ρ) (hCov : TensorCovG (canonSched G) ρ)
    (hL : LinkTSG (canonSched G) W D X ρ w)
    (hnt : ∃ u ∈ HLsG X w, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    (hK : TwoPointKernelG (canonSched G) ρ Gk) (hAF : AFCoefficientG (constsG G) Gk)
    (hNG : NonGaussianTG (canonSched G) ρ) (hND : TensorNondegG (canonSched G) ρ)
    (hAC : ApertureConvG (canonSched G) W D)
    (C : CompositesG G) (wC : TSepG C.Ix τ → X.base.H)
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Z : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTieG ρ Mb Z ∧ TopNormG (canonSched G) (constsG G) Z)
    (hWard : WardTG (canonSched G) ρ) (hCD : CompDataG C) (hCO : CompOSG (canonSched G) C)
    (hLC : LinkCG (canonSched G) X C wC) (hTI : TInG ρ C X w wC)
    (hGen : ObsGenG (canonSched G) W D X) : ClayStatementAtG G W D :=
  clayStatementAtP_of_link (canonSched G) (constsG G) (afConstG_pos G) W D X ρ Gk w hSM hH hRie
    hTie hConv h0 h1 hCov hL hnt hK hAF hNG hND hAC C wC hCT hWard hCD hCO hLC hTI hGen

#print axioms clayStatementAtG_of_link

end Transfer

end MassGap.ClayStatementG

end
