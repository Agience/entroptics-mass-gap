import Mathlib
import MassGap.ZeroFluxGap
import MassGap.InputMerge

/-!
# MassGap.GapFromReads — the sector seed and the run seed from the measured reads, and the Clay statement from them with the other clauses of `NarrowInputsAtMin`

This module collects the gap route into one theorem whose hypotheses are the remaining inputs, each stated in
measured quantities, and it proves the window join that places the flux clause and the zero-flux clause of
`SubstrateFluxRead.SectorSeedMeasured` at one power-of-two side. Declarations are in the namespace
`MassGap.GapFromReads`. Throughout, `m′ = (measMassOf (periodicState hN β) tensorEnergy).toReal` is the measured
mass of the unit channel, and a side `n` is measured by `n m′`.

## The main theorems (proved)

* `sectorSeedMeasured_of_reads`:
  `CoarseReadsFine N hN → LongChainRead N hN → ZeroFluxReadsMass N hN → SectorSeedMeasured hN`.
* `runSeed_of_reads`: the same with `UnitTracksRun hN` gives `WDeltaRun.RunSeed N`.
* `clayStatement_of_reads`: if the four reads hold at every `N ≥ 2` (`ReadsAt N hN2`) and, at every `N ≥ 2`, some
  observer `W` and margin `r` carry the other clauses of `InputMerge.NarrowInputsAtMin` given the run seed
  (`RunSeed N → NarrowInputsAtMin N hN2 W r`), then `MassGap.ClayStatementDy`
  (`InputMerge.clayStatement_of_narrowAtMin`). `RunSeed N` is the last clause of `NarrowInputsAtMin`; the
  hypothesis asks every other clause, and allows them to use the seed.

## The long-chain read (assumed)

**`LongChainRead hN`**: there are a rate `s > 0` and a measured length `D > 0` such that for every measured band
`D′` there is `B` with, eventually in `β`, at every power-of-two side `n ≥ 2` with `D ≤ n m′ ≤ D′`, every direction
`i` and every chain index `j` with `D ≤ 2(j + 1) m′`,

    relayOdds N i (Tr n i) β j ≤ B · e^{−s · 2(j + 1) m′}.

It says that, at an aperture of bounded measured size, the flux odds of the fixed-aperture relay chain fall
exponentially in the measured time extent `2(j + 1) m′` of the chain: confinement read over long chains. The rate
`s` is per measured length; the prefactor `B` may depend on the measured band, not on `β`. It is a sufficient form for the flux clause: `RelayChain.fluxShareN_le_of_coarseReadsFine` multiplies the
long-chain read by `c^l` while the chain grows by `4^l`, so any decay `f` with `c^l f(4^l D₀) → 0` closes it; an
exponential decay in the chain's measured length does (`exists_doublings`), and so would a power `t^{−p}` with
`4^p > c`; a decay with no rate does not in general. The exponential is the form a flux-sector gap gives.

Tests of `LongChainRead`.

1. Degenerate case (proved): at `β = 0` every chain read has odds `0` (`RelayChain.relayOdds_zero_coupling`), so
   the clause holds with every `B ≥ 0` (`longChain_zero_coupling`); the Prop is read along `β → ∞`, so this tests
   the per-coupling clause only.
2. Strong coupling (argued, leading order): a flux sheet winding direction `k` costs `u^{T_k · 2(j + 1)}` and sits
   at `T_l T_m` transverse places, so the odds are a sum of `T_l T_m u^{T_k · 2(j + 1)}`: exponential in the time
   extent at rate `T_k log(1/u)` per lattice length, a prefactor polynomial in the aperture. In measured units the rate is `(σ/m′²) · T m′ ≥ (σ/m′²) D` (`σ` the string tension in lattice units,
`log(1/u)` per unit area at leading order) and, at fixed `β`, the prefactor is bounded on the band `n m′ ≤ D′`. The tree proves
   only upper bounds at strong coupling (`SubstrateFluxRead.sectors_strong`), so this test is not a theorem.
3. Vacuity: `0 < D` is required. At `D ≤ 0` the clause would be asked at the lattice side `n = 2` along `β → ∞`,
   where the aperture is small in measured units, `n m′ → 0`, and the flux energy is sub-additive (the failure
   region of test 3 of `CoarseReadsFine`). With `D > 0` no fixed side meets `D ≤ n m′` once `m′ < D/n`. At
   `m′ = 0` no side meets the clause and the Prop is empty there; the lock `0 < m′` comes from the other inputs.
   `s` is a rate per measured length, `D`, `D′` are measured lengths, `B` is a count. No constant is in
   lattice units.
4. Restatement against reduction: it is neither the flux clause nor implied by it. It is asked at the base
   aperture over chains `4^l` times the side, a read the rectangular tori realize
   (`RelayChain.relayTorus_twoSlice`), and it says nothing about the zero-flux clause. `SectorSeedMeasured` speaks
   of one cubic side, not of long chains at a fixed aperture.
5. Where it could fail (argued): a flux state whose energy does not grow with the time extent (deconfinement at
   small measured aperture, excluded by `D > 0`), or a count of light flux states growing with the aperture
   (excluded by the band `n m′ ≤ D′`, on which `B` may grow).

## The window join (proved)

The two clauses come with windows of different shape.

* Flux (`RelayChain.fluxShareN_le_of_coarseReadsFine`): at every even base side `n ≥ 2` with `C_f ≤ n m′` and
  every `l`, `fluxShareN (2^l n) ≤ c^l · relayOdds (Tr n i) (4^l (n/2) − 1)`.
* Zero-flux (`ZeroFluxGap.zeroFluxClause_of_reads`): at every even side `n ≥ 2` with `C_z ≤ n m′`,
  `trivialDefectN n ≤ 1/80000`.
* Anchor (`measMass_le_of_reads`): the anchor clause `(k + 1) m′ ≤ C₀` of `ZeroFluxReadsMass` forces
  `m′ ≤ C₀`, eventually in `β`.

The join, in `sectorSeedMeasured_of_reads`: set `D₀ = max C_f D` (the flux window and the long-chain window) and
`D′ = max(2D₀, 2C₀)`. `exists_pow_two_window` gives, at each `β`, a base power of two `n₀ = 2^b ≥ 2` with
`D₀ ≤ n₀ m′ ≤ max(2D₀, 2m′) ≤ D′`. `exists_doublings` gives one number of doublings `l`, fixed before `β`, with
`C_z ≤ 2^l D₀` and `c^l · max(B, 0) · e^{−s 4^l D₀} ≤ 1/80000`. The seed side is `n = 2^l n₀`, a power of two:

* the zero-flux clause holds at `n`, since `n m′ ≥ 2^l D₀ ≥ C_z`;
* the flux clause holds at `n`, since `fluxShareN (2^l n₀) ≤ c^l · relayOdds (Tr n₀ i) (j)` with
  `2(j + 1) = 4^l n₀`, and the long-chain read at `n₀` (in its band) gives
  `relayOdds ≤ B e^{−s 4^l n₀ m′} ≤ max(B, 0) e^{−s 4^l D₀}`;
* the window clause holds with `C = 2^l D′`, since `n m′ = 2^l n₀ m′ ≤ 2^l D′`.

So the flux window (a base side, then `l` doublings) and the zero-flux window (every side above `C_z`) meet at
the seed side; the doublings are the shared variable, and the anchor bound `m′ ≤ C₀` caps the base side.

## The remaining inputs

| input | what it says | test status |
|---|---|---|
| `CoarseReadsFine hN` | confinement over long chains: across one aperture doubling, the coarse observer's flux odds over `j` hops are at most `c` times the fine observer's over the relayed `2j + 1` hops, at apertures and chain lengths at least `C₀/m′` | degenerate `β = 0` proved (`exchange_zero_coupling`); strong coupling argued (leading order `c ≈ 4`); flux-tube energies over long chains argued; vacuity check (`C₀ > 0` in measured lengths, lock `0 < m′`) |
| `ZeroFluxReadsMass hN`, gap half | zero-flux gap tie: at every even side with `n m′ ≥ C₂` the zero-flux one-hop kernel has an eigenpair with relative gap per hop at least `c m′` | degenerate `β = 0` proved (`ρ = 0`); strong-coupling shape proved (`trivialDefectN_strong`), no instance; vacuity check (`c` dimensionless) |
| `ZeroFluxReadsMass hN`, anchor half | measured-scale anchor: an anchor index within `C₀` measured lengths has excited zero-flux weight at most `A e^{c n m′/2}` | degenerate `β = 0` proved (weight `0`); extensivity of the one-hop anchor argued, which is why the anchor sits at `C₀/m′` hops; vacuity check |
| `LongChainRead hN` | long-chain read: at bounded measured aperture the relay flux odds fall exponentially in the chain's measured time extent | degenerate `β = 0` proved (`longChain_zero_coupling`); strong coupling argued; vacuity check (`D > 0`) |
| `UnitTracksRun hN` | the measured unit is at least `c₁ · aRun`; needed because `ClayStatement` builds its lattices at spacing `aRun` | no proved test; its reading, asymptotic scaling of one measured mass, is argued; implied by `RunSeed` under the seed floor (`MeasuredSeed.unitTracksAlong_of_runSeedAlong`), and equivalent to it given the measured seed and the floor (`MeasuredSeed.runSeed_iff_unitTracksRun`), the floor assumed; the consumer reads it only along `dyBeta k`, at the steps of `ultra`; not used for `SectorSeedMeasured` |
| `hB` of `clayStatement_of_reads` | every clause of `InputMerge.NarrowInputsAtMin` other than `RunSeed`, given the seed | not addressed in this module |

## Every input of `runSeed_of_reads` is asked only at measured scales

* `CoarseReadsFine`: apertures with every extent `T_k m′ ≥ C₀`, chains with `2(j + 1) m′ ≥ C₀`, `C₀ > 0`.
* `ZeroFluxReadsMass`: sides with `n m′ ≥ C₂`; the anchor index with `(k + 1) m′ ≤ C₀`; the gap in units of `m′`.
  `C₂ ≥ 0` is existential and the clauses are monotone in `C₂`, so the Prop is the same with `C₂ > 0`; no clause
  is forced at a side fixed in lattice units.
* `LongChainRead`: sides with `D ≤ n m′ ≤ D′` and chains with `2(j + 1) m′ ≥ D`, `D > 0`.
* `UnitTracksRun`: a comparison of `m′` with `aRun`, at no side.
* The conclusion `SectorSeedMeasured` asks one side with `n m′ ≤ C`; the side constructed here has
  `n m′ ≥ max(C_f, D, C_z) > 0`.

No input asks a clause at a fixed lattice side.

## Proved, argued, assumed

* Proved: every theorem of the module, with standard axioms only: `exists_pow_two_window`, `exists_doublings`,
  `ofReal_window`, `measMass_le_of_reads`, `longChain_zero_coupling`, `sectorSeedMeasured_of_reads`,
  `runSeed_of_reads`, `runSeed_of_readsAt`, `clayStatement_of_reads`.
* Argued: the strong-coupling readings of `LongChainRead` and `CoarseReadsFine`, the flux-tube energies, the
  extensivity of the one-hop zero-flux anchor.
* Assumed: `CoarseReadsFine`, `LongChainRead`, `ZeroFluxReadsMass` (in `sectorSeedMeasured_of_reads` and after),
  `UnitTracksRun` (in `runSeed_of_reads` and after), and in `clayStatement_of_reads` the other clauses of
  `NarrowInputsAtMin` given the run seed.

## Parameters

| argument | where | status |
|---|---|---|
| `β` (coupling) | every read | shared, in the substrate; the Props are read along `β → ∞` |
| `n` (side), `n₀` (base side) | `LongChainRead`, the join | `n₀` chosen per `β` in `[D₀, D′]` measured; `n = 2^l n₀` |
| `i`, `j` | `LongChainRead` | swept: every direction; every chain with `2(j + 1) m′ ≥ D` |
| `s`, `D` | `LongChainRead` | existential; `s` per measured length, `D` a measured length |
| `D′`, `B` | `LongChainRead` | `D′` swept (a measured band), `B` existential per band |
| `c`, `C_f` | `CoarseReadsFine` | existential; `c ≥ 1` dimensionless, `C_f` measured |
| `C_z`, `C₀` | `ZeroFluxReadsMass` | derived (`zeroFluxClause_of_reads`) and existential, measured |
| `l` (doublings) | the join | derived from the constants only, fixed before `β` |
| `C` | `SectorSeedMeasured` | derived: `2^l D′` |
| `m′` | every read | measured: `(measMassOf (periodicState hN β) tensorEnergy).toReal` |
| `W`, `r` | `clayStatement_of_reads` | existential, as in `NarrowInputsAtMin` |
| `N` | the type | shared with the substrate; `N ≥ 2` in the Clay statement |

DERIVED (module-wide): `2` the least side, the doubling base and the time extent `2(j + 1)`; `4 = 2²` the chain
growth per doubling; `1/80000` the threshold of `SectorSeedMeasured`; `1` the least base exponent and `c ≥ 1`;
`0` the degenerate coupling.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.GapFromReads

open Filter Topology
open scoped ENNReal NNReal
open MassGap.RelayChain (relayOdds CoarseReadsFine fluxShareN_le_of_coarseReadsFine relayOdds_zero_coupling)
open MassGap.ZeroFluxGap (ZeroFluxReadsMass zeroFluxClause_of_reads)
open MassGap.SubstrateFluxRead (SectorSeedMeasured runSeed_of_sectorSeedMeasured)
open MassGap.SubstrateDecode (measMassOf tensorEnergy UnitTracksRun)
open MassGap.PeriodicState (periodicState)
open MassGap.CentreSectorSeedN (fluxShareN trivialDefectN)

/-! ## 1. Real-number steps of the join -/

/-- **A power of two in the window**: for `m > 0` there is `b ≥ 1` with `D ≤ 2^b m ≤ max(2D, 2m)`.
DERIVED: `2` the doubling base; `1` the least exponent. -/
theorem exists_pow_two_window {m D : ℝ} (hm : 0 < m) :
    ∃ b : ℕ, 1 ≤ b ∧ D ≤ 2 ^ b * m ∧ 2 ^ b * m ≤ max (2 * D) (2 * m) := by
  classical
  by_cases h : D ≤ 2 * m
  · exact ⟨1, le_rfl, by simpa using h, by simp⟩
  · replace h : 2 * m < D := not_le.mp h
    have ex : ∃ b : ℕ, D ≤ 2 ^ b * m := by
      obtain ⟨b, hb⟩ := pow_unbounded_of_one_lt (D / m) (one_lt_two : (1 : ℝ) < 2)
      exact ⟨b, ((div_lt_iff₀ hm).mp hb).le⟩
    obtain ⟨b, hb, hmin⟩ : ∃ b : ℕ, D ≤ 2 ^ b * m ∧ ∀ b' < b, ¬ D ≤ 2 ^ b' * m :=
      ⟨Nat.find ex, Nat.find_spec ex, fun b' h' => Nat.find_min ex h'⟩
    have hb2 : 2 ≤ b := by
      by_contra hlt
      have h1 : (2 : ℝ) ^ b ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2 : (2 : ℝ) ^ b * m ≤ 2 ^ 1 * m := mul_le_mul_of_nonneg_right h1 hm.le
      norm_num at h2
      linarith
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have hlt : 2 ^ b' * m < D := not_le.mp (hmin b' (by omega))
    refine ⟨b' + 1, by omega, hb, ?_⟩
    rw [pow_succ]
    have e : 2 ^ b' * 2 * m = 2 * (2 ^ b' * m) := by ring
    rw [e]
    exact le_max_of_le_left (by linarith)

/-- **Enough doublings**: for `c ≥ 1`, `B ≥ 0`, `s > 0`, `D₀ > 0`, `ε > 0` and any `X` there is `l` with
`X ≤ 2^l D₀` and `c^l · B · e^{−s 4^l D₀} ≤ ε`: an exponential decay in a length growing like `4^l` beats `c^l`.
DERIVED: `2` the doubling base; `4 = 2²`; `1` in `l + 1 ≤ 2^l`. -/
theorem exists_doublings {c B s D₀ X ε : ℝ} (hc : 1 ≤ c) (hB : 0 ≤ B) (hs : 0 < s) (hD : 0 < D₀)
    (hε : 0 < ε) :
    ∃ l : ℕ, X ≤ 2 ^ l * D₀ ∧ c ^ l * (B * Real.exp (-(s * (4 ^ l * D₀)))) ≤ ε := by
  set a := s * D₀ with ha
  have ha0 : 0 < a := mul_pos hs hD
  have hQ : 0 < B / ε + 1 := by have := div_nonneg hB hε.le; linarith
  set K := Real.log (B / ε + 1) with hK
  have hK0 : 0 ≤ K := Real.log_nonneg (by have := div_nonneg hB hε.le; linarith)
  set L := Real.log c with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hc
  obtain ⟨l, hl⟩ := pow_unbounded_of_one_lt (max (X / D₀) ((L + K) / a)) (one_lt_two : (1 : ℝ) < 2)
  refine ⟨l, ?_, ?_⟩
  · have h1 : X / D₀ < 2 ^ l := (le_max_left _ _).trans_lt hl
    exact ((div_lt_iff₀ hD).mp h1).le
  · have h2 : L + K ≤ a * 2 ^ l := by
      have h := ((le_max_right _ _).trans_lt hl).le
      rw [div_le_iff₀ ha0] at h
      linarith
    have hl1 : (l : ℝ) + 1 ≤ 2 ^ l := by
      have h : l + 1 ≤ 2 ^ l := Nat.lt_two_pow_self
      exact_mod_cast h
    have e4 : (4 : ℝ) ^ l = 2 ^ l * 2 ^ l := by rw [← mul_pow]; norm_num
    have h3 : (l : ℝ) * L + K ≤ s * (4 ^ l * D₀) := by
      have hp : (0 : ℝ) ≤ 2 ^ l := by positivity
      have h4 : (L + K) * ((l : ℝ) + 1) ≤ (a * 2 ^ l) * 2 ^ l :=
        calc (L + K) * ((l : ℝ) + 1) ≤ (L + K) * 2 ^ l :=
              mul_le_mul_of_nonneg_left hl1 (by linarith)
          _ ≤ (a * 2 ^ l) * 2 ^ l := mul_le_mul_of_nonneg_right h2 hp
      have e : s * (4 ^ l * D₀) = (a * 2 ^ l) * 2 ^ l := by rw [e4, ha]; ring
      rw [e]
      nlinarith [mul_nonneg (Nat.cast_nonneg l : (0 : ℝ) ≤ l) hK0]
    have hcl : c ^ l = Real.exp (l * L) := by
      rw [Real.exp_nat_mul, hL, Real.exp_log (by linarith)]
    have hexp : c ^ l * (B * Real.exp (-(s * (4 ^ l * D₀))))
        = B * Real.exp (l * L - s * (4 ^ l * D₀)) := by
      rw [hcl, sub_eq_add_neg, Real.exp_add]; ring
    rw [hexp]
    have hE : Real.exp (l * L - s * (4 ^ l * D₀)) ≤ (B / ε + 1)⁻¹ := by
      have := Real.exp_le_exp.mpr (show (l : ℝ) * L - s * (4 ^ l * D₀) ≤ -K by linarith)
      rwa [Real.exp_neg, hK, Real.exp_log hQ] at this
    calc B * Real.exp (l * L - s * (4 ^ l * D₀)) ≤ B * (B / ε + 1)⁻¹ :=
          mul_le_mul_of_nonneg_left hE hB
      _ ≤ ε := by
          rw [← div_eq_mul_inv, div_le_iff₀ hQ]
          have e : ε * (B / ε + 1) = B + ε := by field_simp
          rw [e]
          linarith

/-- **A finite measured window in `ℝ≥0∞`**: `n · M = ofReal(n · M.toReal)` for `M ≠ ∞`. DERIVED: no numeral. -/
theorem ofReal_window {M : ℝ≥0∞} (hM : M ≠ ⊤) (n : ℕ) :
    (n : ℝ≥0∞) * M = ENNReal.ofReal ((n : ℝ) * M.toReal) := by
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hM]

/-! ## 2. The long-chain read -/

section Lattice

variable {N : ℕ} [NeZero N]

variable (N) in
/-- **The long-chain read** (assumed): there are a rate `s > 0` per measured length and a measured length
`D > 0` such that for every measured band `D′` there is `B` with, eventually in `β`, at every power-of-two side
`n ≥ 2` with `D ≤ n m′ ≤ D′`, every direction `i` and every chain index `j` with `D ≤ 2(j + 1) m′`, the relay flux
odds at the aperture `Tr n i` over `j` hops are at most `B e^{−s · 2(j + 1) m′}`. DERIVED: `2` the least side and
the time extent `2(j + 1)`; `1` the hop; `0` the signs. -/
def LongChainRead (hN : N ≠ 0) : Prop :=
  ∃ s D : ℝ, 0 < s ∧ 0 < D ∧ ∀ D' : ℝ, ∃ B : ℝ, ∀ᶠ β in atTop,
    ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
      D ≤ (n : ℝ) * (measMassOf (periodicState hN β) tensorEnergy).toReal →
      (n : ℝ) * (measMassOf (periodicState hN β) tensorEnergy).toReal ≤ D' →
      ∀ (i : Fin 4) (j : ℕ),
        D ≤ (2 * ((j : ℝ) + 1)) * (measMassOf (periodicState hN β) tensorEnergy).toReal →
        relayOdds N i (CentreSectorSeed.Tr n i) β j
          ≤ B * Real.exp (-(s * ((2 * ((j : ℝ) + 1)) *
              (measMassOf (periodicState hN β) tensorEnergy).toReal)))

/-- **The long-chain clause at the degenerate coupling**: at `β = 0` the odds are `0`, below every
`B e^{−x}` with `B ≥ 0`. DERIVED: `0`. -/
theorem longChain_zero_coupling {B : ℝ} (hB : 0 ≤ B) (x : ℝ) (i : Fin 4)
    (T : {k : Fin 4 // k ≠ i} → ℕ) (j : ℕ) :
    relayOdds N i T 0 j ≤ B * Real.exp (-x) := by
  rw [relayOdds_zero_coupling]
  exact mul_nonneg hB (Real.exp_pos _).le

/-! ## 3. The anchor caps the measured mass -/

/-- **The anchor caps the measured mass**: under `ZeroFluxReadsMass`, eventually in `β`, `m′ ≤ C₀`, since the
anchor clause `(k + 1) m′ ≤ C₀` is met at some even side above `C₂/m′`. DERIVED: `2` the even side; `1` the hop. -/
theorem measMass_le_of_reads (hN : N ≠ 0) (h : ZeroFluxReadsMass N hN) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ β in atTop, (measMassOf (periodicState hN β) tensorEnergy).toReal ≤ C₀ := by
  obtain ⟨c, -, C₀, hC₀, A, -, C₂, -, hev⟩ := h
  refine ⟨C₀, hC₀, ?_⟩
  filter_upwards [hev] with β hβ
  obtain ⟨hm, hall⟩ := hβ
  set m := (measMassOf (periodicState hN β) tensorEnergy).toReal with hmdef
  have hq : C₂ / m ≤ (⌈C₂ / m⌉₊ : ℝ) := Nat.le_ceil _
  have hqn : (⌈C₂ / m⌉₊ : ℝ) ≤ ((2 * (⌈C₂ / m⌉₊ + 1) : ℕ) : ℝ) := by
    exact_mod_cast (show ⌈C₂ / m⌉₊ ≤ 2 * (⌈C₂ / m⌉₊ + 1) by omega)
  have hCn : C₂ ≤ ((2 * (⌈C₂ / m⌉₊ + 1) : ℕ) : ℝ) * m := (div_le_iff₀ hm).mp (hq.trans hqn)
  obtain ⟨_, _, _, k, -, -, -, hkm, -⟩ :=
    hall (2 * (⌈C₂ / m⌉₊ + 1)) (by omega) ⟨⌈C₂ / m⌉₊ + 1, by omega⟩ hCn 0
  have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
  nlinarith

/-! ## 4. The sector seed from the reads -/

/-- **The sector seed from the measured reads**: the coarse-reads-fine exchange, the long-chain read and the
zero-flux gap reads give `SectorSeedMeasured`. The seed side is `2^l n₀`, `n₀` a power of two in the measured
window `[max C_f D, max(2 max C_f D, 2 C₀)]` and `l` fixed by the constants. DERIVED: `2` the doubling base;
`4 = 2²`; `1/80000` the threshold of `SectorSeedMeasured`; `1` the least base exponent. -/
theorem sectorSeedMeasured_of_reads (hN : N ≠ 0) (hF : CoarseReadsFine N hN) (hL : LongChainRead N hN)
    (hZ : ZeroFluxReadsMass N hN) : SectorSeedMeasured hN := by
  obtain ⟨c, Cf, hc, hCf, hFev⟩ := fluxShareN_le_of_coarseReadsFine hN hF
  obtain ⟨Cz, hZev⟩ := zeroFluxClause_of_reads hN hZ
  obtain ⟨C₀, hC₀, hAev⟩ := measMass_le_of_reads hN hZ
  obtain ⟨s, D, hs, hD, hLall⟩ := hL
  have hD₀ : 0 < max Cf D := lt_max_of_lt_left hCf
  obtain ⟨B, hLev⟩ := hLall (max (2 * max Cf D) (2 * C₀))
  obtain ⟨l, hlz, hlf⟩ := exists_doublings (X := Cz) (ε := 1 / 80000) hc (le_max_right B 0) hs hD₀
    (by norm_num)
  have hD'pos : 0 < max (2 * max Cf D) (2 * C₀) := lt_max_of_lt_left (by linarith)
  refine ⟨2 ^ l * max (2 * max Cf D) (2 * C₀), mul_pos (by positivity) hD'pos, ?_⟩
  filter_upwards [hFev, hZev, hAev, hLev] with β hFβ hZβ hAβ hLβ
  obtain ⟨hm, hZβ⟩ := hZβ
  have hMpos : 0 < measMassOf (periodicState hN β) tensorEnergy ∧
      measMassOf (periodicState hN β) tensorEnergy < ⊤ := ENNReal.toReal_pos_iff.mp hm
  set M := measMassOf (periodicState hN β) tensorEnergy with hMdef
  set m := M.toReal with hmdef
  obtain ⟨b, hb1, hbl, hbu⟩ := exists_pow_two_window (D := max Cf D) hm
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  -- the base side `n₀ = 2^(b'+1)`
  have hn0 : 2 ≤ 2 ^ (b' + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (b' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hen0 : Even (2 ^ (b' + 1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hcast0 : ((2 ^ (b' + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (b' + 1) := by push_cast; ring
  have hlo : max Cf D ≤ ((2 ^ (b' + 1) : ℕ) : ℝ) * m := by rw [hcast0]; exact hbl
  have hhi : ((2 ^ (b' + 1) : ℕ) : ℝ) * m ≤ max (2 * max Cf D) (2 * C₀) := by
    rw [hcast0]
    exact hbu.trans (max_le_max le_rfl (by linarith))
  -- the chain index of the flux bound
  obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = 4 ^ l * (2 ^ (b' + 1) / 2) - 1 := ⟨_, rfl⟩
  have hhalf : 2 ^ (b' + 1) / 2 = 2 ^ b' := by
    rw [pow_succ]; exact Nat.mul_div_cancel _ (by norm_num)
  have hpos1 : 1 ≤ 4 ^ l * 2 ^ b' := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hj : 2 * (j + 1) = 4 ^ l * 2 ^ (b' + 1) := by
    rw [hjdef, hhalf, Nat.sub_add_cancel hpos1, pow_succ]; ring
  have hjr : 2 * ((j : ℝ) + 1) = (4 : ℝ) ^ l * ((2 ^ (b' + 1) : ℕ) : ℝ) := by
    rw [hcast0]; exact_mod_cast hj
  have h4 : (1 : ℝ) ≤ 4 ^ l := one_le_pow₀ (by norm_num)
  have hn0m : 0 ≤ ((2 ^ (b' + 1) : ℕ) : ℝ) * m := by positivity
  have hlong : 4 ^ l * max Cf D ≤ (2 * ((j : ℝ) + 1)) * m := by
    rw [hjr, mul_assoc]
    exact mul_le_mul_of_nonneg_left hlo (by positivity)
  have hDj : D ≤ (2 * ((j : ℝ) + 1)) * m := by
    have : max Cf D ≤ 4 ^ l * max Cf D := le_mul_of_one_le_left hD₀.le h4
    exact (le_max_right Cf D).trans (this.trans hlong)
  -- the seed side `2^l n₀`
  have hcastn : ((2 ^ l * 2 ^ (b' + 1) : ℕ) : ℝ) * m = 2 ^ l * (((2 ^ (b' + 1) : ℕ) : ℝ) * m) := by
    push_cast; ring
  have h2l : (1 : ℝ) ≤ 2 ^ l := one_le_pow₀ (by norm_num)
  refine ⟨hMpos.1, 2 ^ l * 2 ^ (b' + 1), ⟨l + (b' + 1), (pow_add 2 l (b' + 1)).symm⟩, ?_, ?_, fun i => ⟨?_, ?_⟩⟩
  · calc 2 ≤ 2 ^ (b' + 1) := hn0
      _ ≤ 2 ^ l * 2 ^ (b' + 1) := Nat.le_mul_of_pos_left _ (by positivity)
  · rw [ofReal_window hMpos.2.ne, ← hmdef, hcastn]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hhi (by positivity))
  · -- the flux clause
    have hCfE : ENNReal.ofReal Cf ≤ ((2 ^ (b' + 1) : ℕ) : ℝ≥0∞) * M := by
      rw [ofReal_window hMpos.2.ne, ← hmdef]
      exact ENNReal.ofReal_le_ofReal ((le_max_left Cf D).trans hlo)
    have hflux := hFβ (2 ^ (b' + 1)) hn0 hen0 hCfE i l
    rw [← hjdef] at hflux
    have hodds := hLβ (2 ^ (b' + 1)) ⟨b' + 1, rfl⟩ hn0 ((le_max_right Cf D).trans hlo) hhi i j hDj
    have hexp : Real.exp (-(s * ((2 * ((j : ℝ) + 1)) * m))) ≤ Real.exp (-(s * (4 ^ l * max Cf D))) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hlong hs.le))
    have hodds' : relayOdds N i (CentreSectorSeed.Tr (2 ^ (b' + 1)) i) β j
        ≤ max B 0 * Real.exp (-(s * (4 ^ l * max Cf D))) :=
      hodds.trans ((mul_le_mul_of_nonneg_right (le_max_left B 0) (Real.exp_pos _).le).trans
        (mul_le_mul_of_nonneg_left hexp (le_max_right B 0)))
    calc fluxShareN N β (2 ^ l * 2 ^ (b' + 1)) i
        ≤ c ^ l * relayOdds N i (CentreSectorSeed.Tr (2 ^ (b' + 1)) i) β j := hflux
      _ ≤ c ^ l * (max B 0 * Real.exp (-(s * (4 ^ l * max Cf D)))) :=
          mul_le_mul_of_nonneg_left hodds' (pow_nonneg (by linarith) l)
      _ ≤ 1 / 80000 := hlf
  · -- the zero-flux clause
    refine hZβ (2 ^ l * 2 ^ (b' + 1)) ?_ ?_ ?_ i
    · calc 2 ≤ 2 ^ (b' + 1) := hn0
        _ ≤ 2 ^ l * 2 ^ (b' + 1) := Nat.le_mul_of_pos_left _ (by positivity)
    · exact (Nat.even_mul.mpr (Or.inr hen0))
    · rw [hcastn]
      exact hlz.trans (mul_le_mul_of_nonneg_left hlo (by positivity))

/-- **The run seed from the measured reads**: with the unit tracking the supplied spacing.
DERIVED: no numeral. -/
theorem runSeed_of_reads (hN : N ≠ 0) (hF : CoarseReadsFine N hN) (hL : LongChainRead N hN)
    (hZ : ZeroFluxReadsMass N hN) (hU : UnitTracksRun hN) : WDeltaRun.RunSeed N :=
  runSeed_of_sectorSeedMeasured hN (sectorSeedMeasured_of_reads hN hF hL hZ) hU

end Lattice

/-! ## 5. The Clay statement -/

/-- **The four reads at one colour count `N ≥ 2`**. DERIVED: `2` the least colour count. -/
def ReadsAt (N : ℕ) (hN2 : 2 ≤ N) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  CoarseReadsFine N (NeZero.ne N) ∧ LongChainRead N (NeZero.ne N) ∧ ZeroFluxReadsMass N (NeZero.ne N) ∧
    UnitTracksRun (NeZero.ne N)

/-- **The run seed from the reads at one colour count.** DERIVED: `2` the least colour count. -/
theorem runSeed_of_readsAt {N : ℕ} (hN2 : 2 ≤ N) (h : ReadsAt N hN2) : WDeltaRun.RunSeed N := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hF, hL, hZ, hU⟩ := h
  exact runSeed_of_reads (NeZero.ne N) hF hL hZ hU

/-- **The Clay statement from the measured reads and the other per-`N` clauses** (not from the reads alone): if the
four reads hold at every `N ≥ 2` and, at every `N ≥ 2`, some observer and margin carry every other clause of
`NarrowInputsAtMin` (`PhysRange`, `SubstrateCoreMin`, `ExpandR`, `ClusterPM`, `FlowCovLim`, `WardT`,
`ProxyNondeg`, the `ApproxKAt` clause beyond `r`, `ThreePointAtScale`) given the run seed; that is, if the four reads hold at every `N ≥ 2` and, at every
`N ≥ 2`, some observer and margin carry the other clauses of `NarrowInputsAtMin` given the run seed, then
`ClayStatementDy` (`InputMerge.clayStatement_of_narrowAtMin`). DERIVED: `2` the least colour count. -/
theorem clayStatement_of_reads (hR : ∀ (N : ℕ) (hN2 : 2 ≤ N), ReadsAt N hN2)
    (hB : ∀ (N : ℕ) (hN2 : 2 ≤ N), ∃ (W : MassGap.ContinuumFlow.ConfFlow N) (r : ℝ),
      WDeltaRun.RunSeed N → InputMerge.NarrowInputsAtMin N hN2 W r) :
    MassGap.ClayStatementDy :=
  InputMerge.clayStatement_of_narrowAtMin fun N hN2 => by
    obtain ⟨W, r, h⟩ := hB N hN2
    exact ⟨W, r, h (runSeed_of_readsAt hN2 (hR N hN2))⟩

end MassGap.GapFromReads

end

#print axioms MassGap.GapFromReads.exists_pow_two_window
#print axioms MassGap.GapFromReads.exists_doublings
#print axioms MassGap.GapFromReads.ofReal_window
#print axioms MassGap.GapFromReads.longChain_zero_coupling
#print axioms MassGap.GapFromReads.measMass_le_of_reads
#print axioms MassGap.GapFromReads.sectorSeedMeasured_of_reads
#print axioms MassGap.GapFromReads.runSeed_of_reads
#print axioms MassGap.GapFromReads.runSeed_of_readsAt
#print axioms MassGap.GapFromReads.clayStatement_of_reads
