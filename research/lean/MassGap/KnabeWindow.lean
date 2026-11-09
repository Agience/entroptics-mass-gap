import Mathlib
import MassGap.KnabeEngine
import MassGap.WindowRelay

/-!
# MassGap.KnabeWindow — a finite-block certificate at one measured window: a restatement, and a no-go

The frame: the observer holds one channel at a fixed distance from criticality (the band of
`MeasuredTower.MeasTowerG`). What remains of the gap is `SliceTransferGap.TransferGapMeasured`: no sector of
the slice transfer `K = kT` goes light relative to `m′`, at every window `D ≤ n m′`, with an anchor. This module
asks whether that "every window" can be replaced by one finite block at one measured window; it cannot be, in
this form: the comparison is asked at every side and carries the gap. The block is taken past the crossover
(`WindowRelay.PastPeak`), in the way Knabe's criterion replaces a gap at every length by a gap of one patch.
Declarations are in the namespace `MassGap.KnabeWindow`. Throughout `m′ = WindowRelay.mprime two_ne_zero β`
(the measured mass of the `SU(2)` periodic state in lattice units) and `Q(f) = ∫ f (K f)` (`relayForm`).

## 1. What the Knabe criterion proves, and for which operator

`MassGap.KnabeEngine` (namespace `MassGap.KnabeCriterion`) holds the engine: `knabe_bound`, on any module with
a symmetric non-negative form, for a sum `H = Σᵢ hᵢ` of self-adjoint idempotents. A patch gap `γ` gives the gap
`(γ a₁ − a₂ + b − e)/b` of the whole sum, a number fixed by the patch multiplicities and not by the number of
terms. Two operators fit its hypotheses (argued; neither is built in this tree):

* the heat-bath generator `Σ_l (id − E_l)` of the periodic Wilson measure on gauge-invariant observables
  (`E_l` the conditional expectation at link `l`), with box patches of side `n` in four dimensions: Knabe
  constant `(γ n² − 40 n + 36)/(n − 1)²`, and the box gap is one box under every boundary configuration. It is
  frustration-free: every `E_l` fixes the constants, so `H` has the Gibbs vacuum as a common null vector. The
  box gap is argued at `β = 0` (commuting heat baths, gap `1`, every `n ≥ 40`), and on a small-`β` interval
  from a pair-correlation input. Two inputs are open: the box gap itself at the couplings of the tower (the same
  problem at the box scale), and the step from a heat-bath gap to decay of the Wilson state (a
  Guionnet–Zegarlinski statement, not in the literature for lattice gauge theory).
* a nearest-neighbour chain of Hermitian idempotents (local gap threshold `1/m` for windows of `m` terms; a
  path-graph Laplacian, frustration-free and gapless, is the control whose window gap `≤ 1/m` never clears
  it). It stops at the Hamiltonian: the Kogut–Susskind `H = (g²/2) Σ E² − (1/g²) Σ Re tr U_p` has an electric
  and a magnetic term that do not commute and do not share a ground state, so it is not a sum of projections
  with a common null vector. It is frustrated, and a Knabe bound on a frustrated sum bounds the ground energy,
  not a gap.

The slice transfer is frustrated for the same reason (argued). `kT = e^{−β sp/2} gk e^{−β sp/2}`: `gk` is a
convolution in the link variables whose top is the constant function, the outer factors are multiplication
operators peaked at flat spatial plaquettes; the local factors have no common top. `−log K` is not a finite sum
of local terms. No detectability lemma applies to it directly (that lemma needs a frustration-free local sum).

## 2. The criterion chosen, and why

The finite-size criteria with a finite-block hypothesis, read for this operator (argued):

* Martinelli–Olivieri: for finite-range spin systems with compact single-spin space, in every dimension a strong
  mixing condition on the cubes of one side `L` with a large enough rate gives strong mixing in every regular
  volume and a volume-uniform gap of the Glauber dynamics; in two dimensions weak mixing suffices. For gauge
  fields the single-link marginal near a boundary is shifted by a gauge transformation of the boundary, so the
  condition is not met by the link variables as they stand.
* Dobrushin–Shlosman: the constructive finite-box criterion gives complete analyticity in every dimension, and
  with Guionnet–Zegarlinski a uniform gap. Same obstruction.
* Knabe: needs a frustration-free sum. The transfer is not one, but it can be compared with one.

So the criterion here is Knabe's applied to a frustration-free sum of projections, tied to the transfer by a
comparison of quadratic forms. The engine and the compositions are proved; the certificate, the leg (R) and the
anchor (L3) are assumed.

* `H_selfAdj`, `formH_symm`, `formH_sq_le` (proved): `G(u, v) = B(Hu, v)` is symmetric and satisfies
  Cauchy–Schwarz.
* **`poincare_on_range`** (proved): the Knabe form of the gap, `c · B(Hx, x) ≤ B(Hx, Hx)`, is a Poincaré
  inequality on the range: `c · B(y, y) ≤ B(Hy, y)` for every `y = Hx`.
* `BlockCert S M γ c₀` and **`globalGap_of_blockCert`**, **`uniform_globalGap`** (proved): every patch has at
  most `M` terms, `b > 0`, the patch gap is `γ` and the Knabe constant is at least `c₀`; then the whole sum
  has gap `c₀` — for every member of a family, with `c₀` fixed before the family index.
* `SliceCompare i T β S λ φ κ` (definition): a linear map `emb` from functions on the slice into `S.E` with
  `B(emb f, emb f) = ∫ f²`, the comparison `κ |λ| B(H emb f, emb f) ≤ |λ| ∫ f² − Q(f)` on bounded measurable
  `f ⊥ φ`, and `emb f ∈ range H` for those `f`.
* **`relayForm_le_of_compare`** (proved): `SliceCompare` and `GlobalGap c₁` give
  `Q(f) ≤ |λ| (1 − κ c₁) ∫ f²` for every bounded measurable `f ⊥ φ`.

The criterion, composed (`relayForm_le_of_blockCert`, proved):

    BlockCert S M γ c₀ → SliceCompare i T β S λ φ κ → 0 ≤ κ → Measurable f → (∃ B, ∀ x, |f x| ≤ B) →
      ∫ f φ = 0 → Q(f) ≤ |λ| (1 − κ c₀) ∫ f².

## 3. The window certificate (assumed), what it gives, and what it is (proved)

**`WindowCertificate C κ₀ γ c₀`**: eventually in `β`, `m′ > 0` and there is a window `k` with
`C ≤ 2^k m′ ≤ 2C`, past the crossover from `k` on (`PastPeak β k`), such that at every power-of-two side
`n ≥ 2^k` and every direction `i` the slice transfer at aperture `Tr n i` has a top pair `(λ, φ)` and a patch
system `S` with `SliceCompare … S λ φ (κ₀ m′)` and `BlockCert S (3 (2^k)³) γ c₀`. `C`, `κ₀`, `γ`, `c₀` are fixed
before `β`. "One finite block at one measured window" describes only the block size: the block side is `2^k`
lattice units, a fixed `C`–`2C` in measured units; the content (`SliceCompare`, a top pair, a system) is asked at
every side `n ≥ 2^k`.

`globalGap_of_windowCertificate` (proved): the certificate gives the gap `c₀` of the frustration-free sum at
every side `n ≥ 2^k`, uniformly. `rayleigh_of_windowCertificate` (proved): it gives
`Q(f) ≤ |λ| (1 − κ₀ c₀ m′) ∫ f²` on bounded measurable `f ⊥ φ` at every such side.

**The equivalence (proved).** `WindowRayleigh C κ₀` is the per-side Rayleigh bound
`Q(f) ≤ |λ| (1 − κ₀ m′) ∫ f²` with the same window and `PastPeak` clauses. The identity system `idSystem` (one
term `h = id`, one patch, `a₁ = a₂ = b = 1`, `e = 0`, `w = 0`) meets `BlockCert` at every `M ≥ 1`, `c₀ ≤ γ ≤ 1`
(`blockCert_idSystem`), and on the bounded measurable functions of the slice with `B(u, v) = ∫ u v` and `emb`
a projection onto them, `SliceCompare` for it is exactly the Rayleigh bound (`sliceCompare_idSystem`). So
`windowCertificate_of_rayleigh : WindowRayleigh C κ₀ → WindowCertificate C κ₀ γ c₀`
(`c₀ ≤ γ ≤ 1`), `windowRayleigh_of_windowCertificate : WindowCertificate C κ₀ γ c₀ → WindowRayleigh C (κ₀ c₀)`,
and `windowCertificate_iff_rayleigh : WindowCertificate C κ₀ 1 1 ↔ WindowRayleigh C κ₀` at `κ₀ ≥ 0`.
`PatchSystem` does not tie a term to a link, so `BlockCert` carries no gap content in this abstract form.

**`transferGapMeasured_of_windowCertificate`** (proved): `WindowCertificate C κ₀ γ c₀` with `C, κ₀, c₀ > 0`,
the leg `RayleighLeg` and the anchor `AnchorMeasured (κ₀ c₀) (2C)` give
`SliceTransferGap.TransferGapMeasured 2 two_ne_zero` with `c = κ₀ c₀` and `D = 2C`. It repackages
`TransferGapMeasured` into a quadratic-form version plus the anchor; it is correct and is not progress on the
gap.

What is missing, named:

* (R) **`RayleighLeg`** (assumed): from the Rayleigh bound on bounded measurable `f ⊥ φ` at `0 ≤ x ≤ 1` to the
  remainder norm `‖K − λ φ⊗φ‖ ≤ |λ| (1 − x)`. It is functional analysis, not a gap statement (argued): `R` is
  symmetric with `Rφ = 0`, so `⟨f, Rf⟩ = Q(f − ⟨f,φ⟩φ)`; `K ≥ 0` holds for `kT` at `β ≥ 0` (classical
  transfer-matrix positivity: the temporal weight is a positive-definite class function, products of such are
  positive definite by Schur, and the gauge average keeps positivity; argued, not built), so
  `0 ≤ ⟨f, Rf⟩ ≤ |λ|(1 − x)‖f‖²`; the norm of a positive symmetric operator is the supremum of its quadratic
  form, and bounded measurable functions are dense in `L²`.
* (L3) **`AnchorMeasured`** (assumed): the anchor clause of `TransferGapMeasured` for the top pair. A gap
  statement says nothing about it (`SliceTransferGap.no_hop_from_gap`).
* The time direction is not missing: the one-hop transfer is the object here, and a window hop of `j + 1` hops
  is equivalent to it (`WindowRelay.transferGapAt_of_windowHop`, `windowHop_of_transferGapAt`).
* The gap itself: by the equivalence, the identity system meets `BlockCert` at every `M ≥ 1`, and
  `SliceCompare` for it is the Rayleigh bound (`windowCertificate_of_rayleigh`). The certificate is the
  per-side Rayleigh bound.

## 4. The no-go, and the open form

In this abstract form the finite-block certificate carries no gap content: the comparison is asked at every
side, and with the identity system it is the gap's quadratic form. A reduction needs the patch system tied to
the slice. The open form, `LocalWindowCertificate` (stated here in prose, not as a Prop, and assumed nowhere):
`S.E` the bounded measurable functions on the slice with the canonical `emb` and `B(u, v) = ∫ u v`; each `hᵢ`
local to a box of side `L = 2^k` (for example `id` minus the conditional expectation given the links outside a
box), so that a patch gap is one box under every boundary; and the comparison either with `κ` not carrying
`m′`, or proved from local statements rather than asked at every side.

## 5. Tests

1. Strong coupling (proved), at small `β`; no `BlockCert` or `SliceCompare` instance is built, and the
   certificate itself is asked only as `β → ∞`. `strong_block_rate`: at a block slice and `β ≤ β₀(T)` the
   per-slice gap `strong_gap_half` is the leg's conclusion at `x = 1/2`. `strong_every_side`: the uniform
   strong-coupling relay gap (`UniformRelayStrong.uniformRelayGap`) is the conclusion a certificate would give,
   at every side. `betaStrong_lt`: the per-slice Doeblin certificate fails, at any fixed `β > 0`, on some cubic
   slice, so a per-slice gap at one side does not carry to larger sides by itself; a carrying criterion has to
   read a threshold that does not grow with the side.
2. `β = 0` (proved). `zero_coupling_block`: the top pair `(1, 1)` with remainder `0`, the leg's conclusion at every
   `x ≤ 1`, and `PastPeak 0 k` at every `k`. The Prop is read along `β → ∞`, so this tests `TopPair`, the leg's
   conclusion and `PastPeak`, not `SliceCompare` or `BlockCert`.
3. Vacuity (proved). `vacuity_zero_H`: a system with `H = 0` meets `SliceCompare` only if every bounded measurable
   `f ⊥ φ` has `∫ f² = 0`, so the zero system does not certify a slice with a non-constant function; the
   identity system certifies exactly the Rayleigh bound (`sliceCompare_idSystem`, `blockCert_idSystem`).
   `knabeConst_nonpos`: patches whose excess `e` reaches `b`, at `a₁ = a₂ ≥ 0` and `γ ≤ 1`, have Knabe constant
   at most `0`; single-term patches of a sum with non-commuting neighbours are of this kind. `PatchSystem` does
   not tie a term to a link, so the patch-size clause bounds the number of terms in a patch, not their support.
4. Measured scales only (proved and argued). `side_ge_block`: under the certificate the sides read by
   `TransferGapMeasured` with `D = 2C` are at least the block side `2^k`. The certificate is asked only eventually
   in `β`, at the one window with `C ≤ 2^k m′ ≤ 2C`, and past the crossover; nothing at a lattice-unit block and
   nothing before the crossover (the rule "do not let it go supercritical", read as: certify only at the window
   the observer sees on the confined side).
5. Restatement against reduction (proved). It is a restatement: with the identity system it is the per-side
   Rayleigh bound, and conversely (`rayleigh_of_windowCertificate`, `windowCertificate_of_rayleigh`). The gap
   content is in `SliceCompare`; `BlockCert` carries none unless the system is tied to the slice geometry.

## 6. Proved, argued, assumed

* Proved: every theorem of this module and of `MassGap.KnabeEngine`, standard axioms only; in particular the
  equivalence of the certificate with the per-side Rayleigh bound (§3, test 5).
* Argued: the readings of §1 and §2 (the two operators and their open inputs; frustration of the transfer and of
  Kogut–Susskind; the literature criteria and their obstruction for link variables), the truth of (R) including
  `K ≥ 0`, and the open form of §4.
* Assumed: `WindowCertificate`, `RayleighLeg` and `AnchorMeasured`, only in
  `transferGapMeasured_of_windowCertificate`; `WindowCertificate` in `globalGap_of_windowCertificate`,
  `rayleigh_of_windowCertificate` and `windowRayleigh_of_windowCertificate`; `WindowRayleigh` in
  `windowCertificate_of_rayleigh`.

## 7. Parameters

| argument | where | status |
|---|---|---|
| `β` (coupling) | every lattice statement | shared; the certificate is read along `β → ∞` |
| `k`, `L = 2^k` | `WindowCertificate`, `WindowRayleigh` | existential per `β`: the window, `C ≤ L m′ ≤ 2C` |
| `n` (side) | `WindowCertificate`, the leg, the anchor | swept: every power of two `≥ L` |
| `i` (direction), `T` (aperture) | the slice statements | swept; `T = Tr n i` |
| `λ`, `φ` | `TopPair`, `SliceCompare` | existential: the top pair of the slice transfer |
| `S` | `SliceCompare`, `BlockCert` | existential per side: a frustration-free system; `idSystem` in the converse |
| `emb` | `SliceCompare` | existential: functions on the slice into `S.E`; `bddEmb` in the converse |
| `M` | `BlockCert` | the patch size; `3 L³` in the certificate |
| `γ` | `BlockCert`, the certificate | fixed before `β`: the patch gap |
| `c₀` | `BlockCert`, the certificate | fixed before `β`: the Knabe constant floor |
| `κ`, `κ₀` | `SliceCompare`, the certificate | `κ = κ₀ m′`, `κ₀` fixed before `β`: the comparison constant |
| `C` | the certificate | fixed before `β`: the block in measured units |
| `x` | `RayleighLeg` | the relative depth of the Rayleigh bound, in `[0, 1]` |
| `c = κ₀ c₀`, `D = 2C` | `transferGapMeasured_of_windowCertificate` | derived |
| `j₀` | `AnchorMeasured` | existential per side |
| `m′` | everywhere | measured: `WindowRelay.mprime two_ne_zero β` |
| `N` | the slice lemmas, tests | shared; the certificate is at `N = 2`, the carrier of `PastPeak` |

DERIVED (module-wide): `0` the signs and the degenerate coupling; `1` the top, the unit relative depth and the
identity system's weights; `2` the doubling of the window, the gauge group `SU(2)` and the least side; `3` the
dimension of the slice and the links per site; `4` the quarter side of the anchor; `1/2` the strong-coupling
rate.
-/


set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.KnabeWindow

open MeasureTheory Filter Topology
open MassGap MassGap.KnabeCriterion MassGap.RectTransfer MassGap.RectWilson
open MassGap.SliceTransferGap (TransferGapAt TransferGapMeasured transferGapAt_zero_coupling)
open MassGap.SliceCentreAction (Cfg)
open MassGap.RelayChain (relayZ0)
open MassGap.WindowRelay (PastPeak mprime pastPeak_zero_coupling)

/-! ## 1. The Knabe form of the gap is a Poincaré inequality on the range -/

section Range

namespace PatchSystem'

/-- **The whole sum is self-adjoint**: `B(Hu, v) = B(u, Hv)`. DERIVED: no numeral. -/
theorem H_selfAdj (S : PatchSystem) (u v : S.E) : S.B (S.H u) v = S.B u (S.H v) := by
  simp only [PatchSystem.H, totalOp_apply, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => S.selfAdj i u v)

/-- **`G(u, v) = B(Hu, v)` is symmetric.** DERIVED: no numeral. -/
theorem formH_symm (S : PatchSystem) (u v : S.E) : S.B (S.H u) v = S.B (S.H v) u := by
  rw [H_selfAdj, S.symm]

/-- **A non-negative quadratic in `t` has a non-positive discriminant**: `0 ≤ a + 2tb + t²c` for every `t`, with
`0 ≤ c`, gives `b² ≤ a c`. DERIVED: `2` the cross term; `1` the shift that makes the quadratic negative. -/
theorem sq_le_of_quad {a b c : ℝ} (hc : 0 ≤ c) (h : ∀ t : ℝ, 0 ≤ a + 2 * t * b + t ^ 2 * c) :
    b ^ 2 ≤ a * c := by
  rcases hc.lt_or_eq with hc | hc
  · have h1 := h (-b / c)
    have e : a + 2 * (-b / c) * b + (-b / c) ^ 2 * c = a - b ^ 2 / c := by
      field_simp; ring
    rw [e] at h1
    have h2 : b ^ 2 / c ≤ a := by linarith
    rw [div_le_iff₀ hc] at h2
    linarith
  · subst hc
    by_contra hlt
    have hb : b ≠ 0 := by
      intro hb; apply hlt; subst hb; simp
    have h1 := h (-(a + 1) / (2 * b))
    have e : a + 2 * (-(a + 1) / (2 * b)) * b + (-(a + 1) / (2 * b)) ^ 2 * 0 = -1 := by
      field_simp; ring
    rw [e] at h1
    linarith

/-- **Cauchy–Schwarz for `G`**: `B(Hu, v)² ≤ B(Hu, u) B(Hv, v)`. DERIVED: `2` the square. -/
theorem formH_sq_le (S : PatchSystem) (u v : S.E) :
    S.B (S.H u) v ^ 2 ≤ S.B (S.H u) u * S.B (S.H v) v := by
  refine sq_le_of_quad (S.H_form_nonneg v) (fun t => ?_)
  have h := S.H_form_nonneg (u + t • v)
  have e : S.B (S.H (u + t • v)) (u + t • v)
      = S.B (S.H u) u + 2 * t * S.B (S.H u) v + t ^ 2 * S.B (S.H v) v := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [formH_symm S v u]
    ring
  rw [e] at h
  exact h

/-- **The Knabe form of the gap is a Poincaré inequality on the range of `H`**: `c · B(Hx, x) ≤ B(Hx, Hx)` at
every `x` gives `c · B(y, y) ≤ B(Hy, y)` at every `y = Hx`. From Cauchy–Schwarz for `G`:
`B(y, y)² = G(x, y)² ≤ G(x, x) G(y, y) ≤ B(y, y) G(y, y) / c`. DERIVED: `0` the cases on the sign of `c`. -/
theorem poincare_on_range (S : PatchSystem) {c : ℝ} (hg : S.GlobalGap c) (x : S.E) :
    c * S.B (S.H x) (S.H x) ≤ S.B (S.H (S.H x)) (S.H x) := by
  set y := S.H x with hy
  have hyy : 0 ≤ S.B y y := S.nonneg y
  have hGy : 0 ≤ S.B (S.H y) y := S.H_form_nonneg y
  have hGx : 0 ≤ S.B (S.H x) x := S.H_form_nonneg x
  rcases le_or_gt c 0 with hc | hc
  · nlinarith
  rcases hyy.lt_or_eq with hpos | hzero
  · have hcs : S.B y y ^ 2 ≤ S.B (S.H x) x * S.B (S.H y) y := by
      have h := formH_sq_le S x y
      rwa [← hy] at h
    have hgx : c * S.B (S.H x) x ≤ S.B y y := hg x
    have h1 : c * S.B y y ^ 2 ≤ S.B y y * S.B (S.H y) y := by
      calc c * S.B y y ^ 2 ≤ c * (S.B (S.H x) x * S.B (S.H y) y) := mul_le_mul_of_nonneg_left hcs hc.le
        _ = (c * S.B (S.H x) x) * S.B (S.H y) y := by ring
        _ ≤ S.B y y * S.B (S.H y) y := mul_le_mul_of_nonneg_right hgx hGy
    have h2 : S.B y y * (c * S.B y y) ≤ S.B y y * S.B (S.H y) y := by nlinarith
    exact le_of_mul_le_mul_left h2 hpos
  · rw [← hzero]; simpa using hGy

end PatchSystem'

end Range

/-! ## 2. The block certificate and the uniform gap -/

section Block

open Classical in
/-- The number of terms with non-zero weight in patch `k`. DERIVED: `0` the weight. -/
def patchSize (S : PatchSystem) (k : S.κ) : ℕ := (Finset.univ.filter fun i => S.c k i ≠ 0).card

/-- **The block certificate**: every patch has at most `M` terms, `b > 0`, every patch has gap `γ`, and the
Knabe constant is at least `c₀`. DERIVED: `0` the sign of `b`. -/
def BlockCert (S : PatchSystem) (M : ℕ) (γ c₀ : ℝ) : Prop :=
  (∀ k, patchSize S k ≤ M) ∧ 0 < S.b ∧ S.LocalGap γ ∧ c₀ ≤ S.knabeConst γ

/-- **A block certificate gives the gap of the whole sum** (`globalGap_of_localGap`, `globalGap_mono`).
DERIVED: no numeral. -/
theorem globalGap_of_blockCert {S : PatchSystem} {M : ℕ} {γ c₀ : ℝ} (h : BlockCert S M γ c₀) :
    S.GlobalGap c₀ :=
  S.globalGap_mono h.2.2.2 (S.globalGap_of_localGap h.2.1 h.2.2.1)

/-- **Finite blocks give the gap of every member of a family, uniformly**: one `M`, `γ`, `c₀` for every index.
DERIVED: no numeral. -/
theorem uniform_globalGap {ι : Type*} (F : ι → PatchSystem) {M : ℕ} {γ c₀ : ℝ}
    (h : ∀ n, BlockCert (F n) M γ c₀) : ∀ n, (F n).GlobalGap c₀ :=
  fun n => globalGap_of_blockCert (h n)

/-- **A patch system whose excess reaches `b` certifies nothing**: at `a₁ = a₂ ≥ 0`, `γ ≤ 1`, `0 < b ≤ e`, the
Knabe constant is at most `0`. DERIVED: `0`, `1`. -/
theorem knabeConst_nonpos (S : PatchSystem) {γ : ℝ} (ha : S.a₁ = S.a₂) (ha0 : 0 ≤ S.a₁) (hγ : γ ≤ 1)
    (hb : 0 < S.b) (he : S.b ≤ S.e) : S.knabeConst γ ≤ 0 := by
  unfold PatchSystem.knabeConst
  refine div_nonpos_of_nonpos_of_nonneg ?_ hb.le
  rw [← ha]
  nlinarith

end Block

/-! ## 3. The comparison with the slice transfer -/

section Compare

variable {N : ℕ} [NeZero N]

variable (N) in
/-- **The quadratic form of the slice transfer**: `Q(f) = ∫ f (K f)`. DERIVED: no numeral. -/
def relayForm (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β : ℝ) (f : Cfg i T N → ℝ) : ℝ :=
  ∫ x, f x * ∫ y, kT i T N β x y * f y ∂(hS i T N) ∂(hS i T N)

variable (N) in
/-- **A top pair of the slice transfer**: `φ` bounded measurable, unit, eigenfunction at `λ ≠ 0` (the first five
clauses of `TransferGapAt`). DERIVED: `1` the normalization; `0`. -/
def TopPair (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β lam : ℝ) (φ : Cfg i T N → ℝ) : Prop :=
  Measurable φ ∧ (∃ B : ℝ, ∀ x, |φ x| ≤ B) ∧ ∫ x, φ x ^ 2 ∂(hS i T N) = 1 ∧ lam ≠ 0 ∧
    ∀ z, ∫ y, kT i T N β z y * φ y ∂(hS i T N) = lam * φ z

variable (N) in
/-- **The slice transfer compares with a frustration-free system**: a linear `emb` from functions on the slice
into `S.E` with `B(emb f, emb f) = ∫ f²`, the comparison `κ |λ| B(H emb f, emb f) ≤ |λ| ∫ f² − Q(f)`, and
`emb f` in the range of `H`, at every bounded measurable `f ⊥ φ`. DERIVED: `2` the square. -/
def SliceCompare (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β : ℝ) (S : PatchSystem) (lam : ℝ)
    (φ : Cfg i T N → ℝ) (κ : ℝ) : Prop :=
  ∃ emb : (Cfg i T N → ℝ) →ₗ[ℝ] S.E,
    (∀ f : Cfg i T N → ℝ, Measurable f → (∃ B : ℝ, ∀ x, |f x| ≤ B) →
      S.B (emb f) (emb f) = ∫ x, f x ^ 2 ∂(hS i T N)) ∧
    (∀ f : Cfg i T N → ℝ, Measurable f → (∃ B : ℝ, ∀ x, |f x| ≤ B) →
      ∫ x, f x * φ x ∂(hS i T N) = 0 →
      κ * |lam| * S.B (S.H (emb f)) (emb f) ≤ |lam| * ∫ x, f x ^ 2 ∂(hS i T N) - relayForm N i T β f) ∧
    (∀ f : Cfg i T N → ℝ, Measurable f → (∃ B : ℝ, ∀ x, |f x| ≤ B) →
      ∫ x, f x * φ x ∂(hS i T N) = 0 → ∃ y, S.H y = emb f)

variable {i : Fin 4} {T : {k : Fin 4 // k ≠ i} → ℕ} {β : ℝ}

/-- **The comparison and the gap of the frustration-free sum bound the transfer's Rayleigh quotient**:
`Q(f) ≤ |λ| (1 − κ c₁) ∫ f²` at every bounded measurable `f ⊥ φ` (`poincare_on_range` at a preimage of
`emb f`). DERIVED: `1` the top. -/
theorem relayForm_le_of_compare {S : PatchSystem} {lam κ c₁ : ℝ} {φ : Cfg i T N → ℝ}
    (hcmp : SliceCompare N i T β S lam φ κ) (hκ : 0 ≤ κ) (hg : S.GlobalGap c₁)
    {f : Cfg i T N → ℝ} (hfm : Measurable f) (hfb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hfφ : ∫ x, f x * φ x ∂(hS i T N) = 0) :
    relayForm N i T β f ≤ |lam| * (1 - κ * c₁) * ∫ x, f x ^ 2 ∂(hS i T N) := by
  obtain ⟨emb, hnorm, hle, hon⟩ := hcmp
  obtain ⟨y, hy⟩ := hon f hfm hfb hfφ
  have hP := PatchSystem'.poincare_on_range S hg y
  rw [hy, hnorm f hfm hfb] at hP
  have hc := hle f hfm hfb hfφ
  have hk : 0 ≤ κ * |lam| := mul_nonneg hκ (abs_nonneg _)
  have h1 := mul_le_mul_of_nonneg_left hP hk
  nlinarith

/-- **The criterion, composed**: a block certificate and the comparison give the Rayleigh bound
`Q(f) ≤ |λ| (1 − κ c₀) ∫ f²` on bounded measurable `f ⊥ φ`. DERIVED: `1` the top. -/
theorem relayForm_le_of_blockCert {S : PatchSystem} {M : ℕ} {γ c₀ lam κ : ℝ} {φ : Cfg i T N → ℝ}
    (hB : BlockCert S M γ c₀) (hcmp : SliceCompare N i T β S lam φ κ) (hκ : 0 ≤ κ)
    {f : Cfg i T N → ℝ} (hfm : Measurable f) (hfb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hfφ : ∫ x, f x * φ x ∂(hS i T N) = 0) :
    relayForm N i T β f ≤ |lam| * (1 - κ * c₀) * ∫ x, f x ^ 2 ∂(hS i T N) :=
  relayForm_le_of_compare hcmp hκ (globalGap_of_blockCert hB) hfm hfb hfφ

/-- **Vacuity: the zero system certifies only a slice with no non-constant function**: if `H = 0`, the range
clause forces `emb f = 0`, so `∫ f² = 0` for every bounded measurable `f ⊥ φ`. DERIVED: `2`, `0`. -/
theorem vacuity_zero_H {S : PatchSystem} {lam κ : ℝ} {φ : Cfg i T N → ℝ}
    (hcmp : SliceCompare N i T β S lam φ κ) (hH : ∀ y, S.H y = 0)
    {f : Cfg i T N → ℝ} (hfm : Measurable f) (hfb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hfφ : ∫ x, f x * φ x ∂(hS i T N) = 0) : ∫ x, f x ^ 2 ∂(hS i T N) = 0 := by
  obtain ⟨emb, hnorm, -, hon⟩ := hcmp
  obtain ⟨y, hy⟩ := hon f hfm hfb hfφ
  rw [← hnorm f hfm hfb, ← hy, hH y, map_zero]

end Compare

/-! ## 4. The window certificate in measured units -/

section Window

/-- The links of a box of side `L` in the three-dimensional slice. DERIVED: `3` the dimension and the links per
site. -/
def blockTerms (L : ℕ) : ℕ := 3 * L ^ 3

/-- **`WindowCertificate C κ₀ γ c₀`** (assumed): eventually in `β`, `m′ > 0` and there is a window `k` with
`C ≤ 2^k m′ ≤ 2C`, past the crossover from `k` on, such that at every power-of-two side `n ≥ 2^k` and every
direction the slice transfer at `Tr n i` has a top pair and a frustration-free system of blocks of side `2^k`
that it compares with at `κ = κ₀ m′`, with patch gap `γ` and Knabe constant at least `c₀`.
DERIVED: `2` the doubling and the gauge group. -/
def WindowCertificate (C κ₀ γ c₀ : ℝ) : Prop :=
  ∀ᶠ β in atTop, 0 < mprime (M := 2) two_ne_zero β ∧ ∃ k : ℕ,
    C ≤ (2 : ℝ) ^ k * mprime (M := 2) two_ne_zero β ∧
    (2 : ℝ) ^ k * mprime (M := 2) two_ne_zero β ≤ 2 * C ∧ PastPeak β k ∧
    ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ^ k ≤ n → ∀ i : Fin 4,
      ∃ lam : ℝ, ∃ φ : Cfg i (CentreSectorSeed.Tr n i) 2 → ℝ, ∃ S : PatchSystem,
        TopPair 2 i (CentreSectorSeed.Tr n i) β lam φ ∧
        SliceCompare 2 i (CentreSectorSeed.Tr n i) β S lam φ (κ₀ * mprime (M := 2) two_ne_zero β) ∧
        BlockCert S (blockTerms (2 ^ k)) γ c₀

/-- **(R) The Rayleigh leg** (assumed): at every side and direction, a top pair whose Rayleigh quotient on bounded
measurable `f ⊥ φ` is at most `|λ| (1 − x)`, `0 ≤ x ≤ 1`, has remainder norm at most `|λ| (1 − x)`.
DERIVED: `1` the top. -/
def RayleighLeg : Prop :=
  ∀ᶠ β in atTop, ∀ (n : ℕ) (i : Fin 4) (lam : ℝ) (φ : Cfg i (CentreSectorSeed.Tr n i) 2 → ℝ) (x : ℝ),
    0 ≤ x → x ≤ 1 → TopPair 2 i (CentreSectorSeed.Tr n i) β lam φ →
    (∀ f : Cfg i (CentreSectorSeed.Tr n i) 2 → ℝ, Measurable f → (∃ B : ℝ, ∀ z, |f z| ≤ B) →
      ∫ z, f z * φ z ∂(hS i (CentreSectorSeed.Tr n i) 2) = 0 →
      relayForm 2 i (CentreSectorSeed.Tr n i) β f
        ≤ |lam| * (1 - x) * ∫ z, f z ^ 2 ∂(hS i (CentreSectorSeed.Tr n i) 2)) →
    ∃ ρ : ℝ, TransferGapAt 2 i (CentreSectorSeed.Tr n i) β lam φ ρ ∧ ρ ≤ |lam| * (1 - x)

/-- **(L3) The anchor along the measured tower** (assumed): at every power-of-two side `n ≥ 2` with `D ≤ n m′`,
every gapped pair (`ρ < |λ|`) has an anchor `j₀` in the first quarter of the chain at which the zero-flux hop
rate is within `e^{−c m′}` of `λ²`. DERIVED: `2` the least side and the square; `4` the quarter side. -/
def AnchorMeasured (c D : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    D ≤ (n : ℝ) * mprime (M := 2) two_ne_zero β → ∀ (i : Fin 4) (lam : ℝ)
    (φ : Cfg i (CentreSectorSeed.Tr n i) 2 → ℝ) (ρ : ℝ),
    TransferGapAt 2 i (CentreSectorSeed.Tr n i) β lam φ ρ → ρ < |lam| →
    ∃ j₀ : ℕ, 4 * (j₀ + 1) ≤ n ∧
      lam ^ 2 * relayZ0 2 i (CentreSectorSeed.Tr n i) β j₀
        ≤ Real.exp (c * mprime (M := 2) two_ne_zero β) * relayZ0 2 i (CentreSectorSeed.Tr n i) β (j₀ + 1)

/-- **The sides read at `D = 2C` lie above the block**: `2^k m′ ≤ 2C ≤ n m′` and `m′ > 0` give `2^k ≤ n`.
DERIVED: `2` the doubling. -/
theorem side_ge_block {C m : ℝ} {k n : ℕ} (hm : 0 < m) (hk : (2 : ℝ) ^ k * m ≤ 2 * C)
    (hn : 2 * C ≤ (n : ℝ) * m) : 2 ^ k ≤ n := by
  have h : (2 : ℝ) ^ k ≤ n := le_of_mul_le_mul_right (hk.trans hn) hm
  exact_mod_cast h

/-- **The certificate gives the frustration-free gap at every side above the block, uniformly.**
DERIVED: `2` the doubling. -/
theorem globalGap_of_windowCertificate {C κ₀ γ c₀ : ℝ} (hW : WindowCertificate C κ₀ γ c₀) :
    ∀ᶠ β in atTop, ∃ k : ℕ, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ^ k ≤ n → ∀ i : Fin 4,
      ∃ lam : ℝ, ∃ φ : Cfg i (CentreSectorSeed.Tr n i) 2 → ℝ, ∃ S : PatchSystem,
        TopPair 2 i (CentreSectorSeed.Tr n i) β lam φ ∧ S.GlobalGap c₀ := by
  filter_upwards [hW] with β hβ
  obtain ⟨-, k, -, -, -, h⟩ := hβ
  refine ⟨k, fun n hn hkn i => ?_⟩
  obtain ⟨lam, φ, S, htop, -, hB⟩ := h n hn hkn i
  exact ⟨lam, φ, S, htop, globalGap_of_blockCert hB⟩

/-- **The certificate gives the Rayleigh bound `Q(f) ≤ |λ| (1 − κ₀ c₀ m′) ∫ f²` at every side above the block.**
DERIVED: `2` the doubling. -/
theorem rayleigh_of_windowCertificate {C κ₀ γ c₀ : ℝ} (hκ : 0 ≤ κ₀) (hW : WindowCertificate C κ₀ γ c₀) :
    ∀ᶠ β in atTop, ∃ k : ℕ, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ^ k ≤ n → ∀ i : Fin 4,
      ∃ lam : ℝ, ∃ φ : Cfg i (CentreSectorSeed.Tr n i) 2 → ℝ,
        TopPair 2 i (CentreSectorSeed.Tr n i) β lam φ ∧
        ∀ f : Cfg i (CentreSectorSeed.Tr n i) 2 → ℝ, Measurable f → (∃ B : ℝ, ∀ z, |f z| ≤ B) →
          ∫ z, f z * φ z ∂(hS i (CentreSectorSeed.Tr n i) 2) = 0 →
          relayForm 2 i (CentreSectorSeed.Tr n i) β f
            ≤ |lam| * (1 - κ₀ * mprime (M := 2) two_ne_zero β * c₀)
              * ∫ z, f z ^ 2 ∂(hS i (CentreSectorSeed.Tr n i) 2) := by
  filter_upwards [hW] with β hβ
  obtain ⟨hm, k, -, -, -, h⟩ := hβ
  refine ⟨k, fun n hn hkn i => ?_⟩
  obtain ⟨lam, φ, S, htop, hcmp, hB⟩ := h n hn hkn i
  exact ⟨lam, φ, htop, fun f hfm hfb hfφ =>
    relayForm_le_of_blockCert hB hcmp (mul_nonneg hκ hm.le) hfm hfb hfφ⟩

/-- **The window certificate, the Rayleigh leg and the anchor give `TransferGapMeasured`** at `N = 2`, with
`c = κ₀ c₀` and `D = 2C`. The leg is applied at `x = min(κ₀ c₀ m′, 1)`; `1 − x ≤ e^{−κ₀ c₀ m′}`.
DERIVED: `1` the cap of `x`; `2` the window. -/
theorem transferGapMeasured_of_windowCertificate {C κ₀ γ c₀ : ℝ} (hC : 0 < C) (hκ : 0 < κ₀) (hc₀ : 0 < c₀)
    (hW : WindowCertificate C κ₀ γ c₀) (hR : RayleighLeg) (hA : AnchorMeasured (κ₀ * c₀) (2 * C)) :
    TransferGapMeasured 2 two_ne_zero := by
  refine ⟨κ₀ * c₀, mul_pos hκ hc₀, 2 * C, by linarith, ?_⟩
  filter_upwards [hW, hR, hA] with β hβ hRβ hAβ
  obtain ⟨hm, k, -, hk2, -, h⟩ := hβ
  refine ⟨hm, fun n hn h2 hDn i => ?_⟩
  have hkn : 2 ^ k ≤ n := side_ge_block hm hk2 hDn
  obtain ⟨lam, φ, S, htop, hcmp, hB⟩ := h n hn hkn i
  set m := mprime (M := 2) two_ne_zero β with hmdef
  set x := min (κ₀ * m * c₀) 1 with hx
  have hx0 : 0 ≤ x := le_min (by positivity) zero_le_one
  have hx1 : x ≤ 1 := min_le_right _ _
  have hxpos : 0 < x := lt_min (by positivity) one_pos
  have hray : ∀ f : Cfg i (CentreSectorSeed.Tr n i) 2 → ℝ, Measurable f → (∃ B : ℝ, ∀ z, |f z| ≤ B) →
      ∫ z, f z * φ z ∂(hS i (CentreSectorSeed.Tr n i) 2) = 0 →
      relayForm 2 i (CentreSectorSeed.Tr n i) β f
        ≤ |lam| * (1 - x) * ∫ z, f z ^ 2 ∂(hS i (CentreSectorSeed.Tr n i) 2) := by
    intro f hfm hfb hfφ
    have h1 := relayForm_le_of_blockCert hB hcmp (mul_nonneg hκ.le hm.le) hfm hfb hfφ
    have hI : 0 ≤ ∫ z, f z ^ 2 ∂(hS i (CentreSectorSeed.Tr n i) 2) :=
      integral_nonneg (fun z => sq_nonneg _)
    have hxle : x ≤ κ₀ * m * c₀ := min_le_left _ _
    have h3 : |lam| * (1 - κ₀ * m * c₀) * ∫ z, f z ^ 2 ∂(hS i (CentreSectorSeed.Tr n i) 2)
        ≤ |lam| * (1 - x) * ∫ z, f z ^ 2 ∂(hS i (CentreSectorSeed.Tr n i) 2) := by
      have : |lam| * (1 - κ₀ * m * c₀) ≤ |lam| * (1 - x) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      exact mul_le_mul_of_nonneg_right this hI
    exact h1.trans h3
  obtain ⟨ρ, hgap, hρ⟩ := hRβ n i lam φ x hx0 hx1 htop hray
  have hl : 0 < |lam| := abs_pos.mpr htop.2.2.2.1
  have hρlt : ρ < |lam| := by
    calc ρ ≤ |lam| * (1 - x) := hρ
      _ < |lam| * 1 := mul_lt_mul_of_pos_left (by linarith) hl
      _ = |lam| := mul_one _
  obtain ⟨j₀, hj₀, hanc⟩ := hAβ n hn h2 hDn i lam φ ρ hgap hρlt
  refine ⟨lam, φ, ρ, j₀, hgap, ?_, hj₀, hanc⟩
  -- `1 − x ≤ e^{−κ₀ c₀ m}`
  have hexp : 1 - x ≤ Real.exp (-(κ₀ * c₀ * m)) := by
    rcases le_total (κ₀ * m * c₀) 1 with hle | hle
    · have hxe : x = κ₀ * m * c₀ := min_eq_left hle
      have := Real.add_one_le_exp (-(κ₀ * c₀ * m))
      rw [hxe]; nlinarith
    · have hxe : x = 1 := min_eq_right hle
      rw [hxe, sub_self]; exact (Real.exp_pos _).le
  calc ρ ≤ |lam| * (1 - x) := hρ
    _ ≤ |lam| * Real.exp (-(κ₀ * c₀ * m)) := mul_le_mul_of_nonneg_left hexp (abs_nonneg _)

end Window

/-! ## 4b. The identity system: the certificate is the per-side Rayleigh bound -/

section Identity

/-- **The identity system** on a module with a symmetric non-negative form: one term `h = id`, one patch of
weight `1`, `a₁ = a₂ = b = 1`, `e = 0`, `w = 0`. DERIVED: `1`, `0` the weights. -/
def idSystem {E : Type} [AddCommGroup E] [Module ℝ E] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hs : ∀ x y, B x y = B y x) (hn : ∀ x, 0 ≤ B x x) : PatchSystem where
  E := E
  ι := Unit
  κ := Unit
  B := B
  symm := hs
  nonneg := hn
  h := fun _ => LinearMap.id
  selfAdj := fun _ _ _ => rfl
  idem := fun _ _ => rfl
  c := fun _ _ => 1
  w := fun _ _ => 0
  a₁ := 1
  a₂ := 1
  b := 1
  e := 0
  cover := by intro i; simp
  cover2 := by intro i; simp [pairWeight]
  pair := fun i j hij => absurd (Subsingleton.elim i j) hij
  w_nonneg := fun _ _ => le_rfl
  row := by intro i; simp
  col := by intro j; simp

section IdLemmas

variable {E : Type} [AddCommGroup E] [Module ℝ E] {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ}
  {hs : ∀ x y, B x y = B y x} {hn : ∀ x, 0 ≤ B x x}

/-- `H = id` for the identity system. DERIVED: no numeral. -/
theorem idSystem_H (x : E) : (idSystem B hs hn).H x = x := by
  show totalOp (idSystem B hs hn).h x = x
  rw [totalOp_apply]
  show ∑ _i : Unit, (LinearMap.id : E →ₗ[ℝ] E) x = x
  simp

/-- **The identity system meets `BlockCert` at every `M ≥ 1` and `c₀ ≤ γ ≤ 1`.** DERIVED: `1`. -/
theorem blockCert_idSystem {M : ℕ} (hM : 1 ≤ M) {γ c₀ : ℝ} (hγ : γ ≤ 1) (hc : c₀ ≤ γ) :
    BlockCert (idSystem B hs hn) M γ c₀ := by
  refine ⟨fun k => ?_, by simp [idSystem], fun k x => ?_, ?_⟩
  · unfold patchSize
    refine le_trans (le_of_eq ?_) hM
    simp [idSystem]
  · have hA : (idSystem B hs hn).A k x = x := by
      show patchOp (idSystem B hs hn).c (idSystem B hs hn).h k x = x
      rw [patchOp_apply]
      show ∑ _i : Unit, (1 : ℝ) • (LinearMap.id : E →ₗ[ℝ] E) x = x
      simp
    rw [hA]
    have := (idSystem B hs hn).nonneg x
    nlinarith
  · unfold PatchSystem.knabeConst
    simp only [idSystem]
    simpa using hc

end IdLemmas

variable {N : ℕ} [NeZero N]

variable (N) in
/-- The bounded measurable functions on the slice, as a submodule. DERIVED: `0` the bound of `0`. -/
def bddSub (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) : Submodule ℝ (Cfg i T N → ℝ) where
  carrier := {f | Measurable f ∧ ∃ B : ℝ, ∀ x, |f x| ≤ B}
  add_mem' := by
    rintro f g ⟨hf, Bf, hBf⟩ ⟨hg, Bg, hBg⟩
    exact ⟨hf.add hg, Bf + Bg, fun x => (abs_add_le _ _).trans (add_le_add (hBf x) (hBg x))⟩
  zero_mem' := ⟨measurable_const, 0, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨hf, Bf, hBf⟩
    refine ⟨hf.const_smul c, |c| * Bf, fun x => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hBf x) (abs_nonneg c)

variable {i : Fin 4} {T : {k : Fin 4 // k ≠ i} → ℕ}

/-- The product of two bounded measurable functions is integrable. DERIVED: no numeral. -/
theorem integrable_bddSub (u v : bddSub N i T) :
    Integrable (fun x => (u : Cfg i T N → ℝ) x * (v : Cfg i T N → ℝ) x) (hS i T N) := by
  obtain ⟨hu, Bu, hBu⟩ := u.2
  obtain ⟨hv, Bv, hBv⟩ := v.2
  refine KernelPower.integrable_of_bdd (hu.mul hv) (C := Bu * Bv) (fun x => ?_)
  rw [abs_mul]
  exact mul_le_mul (hBu x) (hBv x) (abs_nonneg _) ((abs_nonneg _).trans (hBu x))

variable (N i T) in
/-- **The `L²` form on the bounded measurable functions**: `B(u, v) = ∫ u v`. DERIVED: no numeral. -/
def l2Form : bddSub N i T →ₗ[ℝ] bddSub N i T →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => ∫ x, (u : Cfg i T N → ℝ) x * (v : Cfg i T N → ℝ) x ∂(hS i T N))
    (fun u₁ u₂ v => by
      simp only [Submodule.coe_add, Pi.add_apply, add_mul]
      exact integral_add (integrable_bddSub u₁ v) (integrable_bddSub u₂ v))
    (fun c u v => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul c _)
    (fun u v₁ v₂ => by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add]
      exact integral_add (integrable_bddSub u v₁) (integrable_bddSub u v₂))
    (fun c u v => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
      exact integral_const_mul c _)

theorem l2Form_apply (u v : bddSub N i T) :
    l2Form N i T u v = ∫ x, (u : Cfg i T N → ℝ) x * (v : Cfg i T N → ℝ) x ∂(hS i T N) := rfl

theorem l2Form_symm (u v : bddSub N i T) : l2Form N i T u v = l2Form N i T v u := by
  simp only [l2Form_apply, mul_comm]

theorem l2Form_nonneg (u : bddSub N i T) : 0 ≤ l2Form N i T u u :=
  integral_nonneg (fun _ => mul_self_nonneg _)

variable (N i T) in
/-- **A linear projection of all functions on the slice onto the bounded measurable ones**
(`Submodule.exists_isCompl`, `LinearMap.linearProjOfIsCompl`). DERIVED: no numeral. -/
def bddEmb : (Cfg i T N → ℝ) →ₗ[ℝ] bddSub N i T :=
  LinearMap.linearProjOfIsCompl (Classical.choose (Submodule.exists_isCompl (bddSub N i T)))
    (bddSub N i T).subtype Subtype.val_injective
    (by rw [Submodule.range_subtype]; exact Classical.choose_spec (Submodule.exists_isCompl (bddSub N i T)))

/-- The projection is the identity on bounded measurable functions. DERIVED: no numeral. -/
theorem bddEmb_apply {f : Cfg i T N → ℝ} (hf : f ∈ bddSub N i T) : bddEmb N i T f = ⟨f, hf⟩ := by
  have := LinearMap.linearProjOfIsCompl_apply_left
    (Classical.choose (Submodule.exists_isCompl (bddSub N i T)))
    (bddSub N i T).subtype Subtype.val_injective
    (by rw [Submodule.range_subtype]; exact Classical.choose_spec (Submodule.exists_isCompl (bddSub N i T)))
    ⟨f, hf⟩
  exact this

variable (N i T) in
/-- **The identity system on the bounded measurable functions of the slice.** DERIVED: no numeral. -/
def sliceIdSystem : PatchSystem := idSystem (l2Form N i T) l2Form_symm l2Form_nonneg

/-- **For the identity system, `SliceCompare` is the Rayleigh bound**: `Q(f) ≤ |λ| (1 − κ) ∫ f²` on bounded
measurable `f ⊥ φ` gives `SliceCompare … (sliceIdSystem) λ φ κ`. DERIVED: `1`, `2`. -/
theorem sliceCompare_idSystem {β lam κ : ℝ} {φ : Cfg i T N → ℝ}
    (h : ∀ f : Cfg i T N → ℝ, Measurable f → (∃ B : ℝ, ∀ x, |f x| ≤ B) →
      ∫ x, f x * φ x ∂(hS i T N) = 0 →
      relayForm N i T β f ≤ |lam| * (1 - κ) * ∫ x, f x ^ 2 ∂(hS i T N)) :
    SliceCompare N i T β (sliceIdSystem N i T) lam φ κ := by
  have hnorm : ∀ f : Cfg i T N → ℝ, Measurable f → (∃ B : ℝ, ∀ x, |f x| ≤ B) →
      l2Form N i T (bddEmb N i T f) (bddEmb N i T f) = ∫ x, f x ^ 2 ∂(hS i T N) := by
    intro f hfm hfb
    rw [bddEmb_apply (f := f) ⟨hfm, hfb⟩, l2Form_apply]
    simp only [pow_two]
  refine ⟨bddEmb N i T, hnorm, fun f hfm hfb hfφ => ?_, fun f _ _ _ => ⟨bddEmb N i T f, idSystem_H _⟩⟩
  have hH : (sliceIdSystem N i T).H (bddEmb N i T f) = bddEmb N i T f := idSystem_H _
  show κ * |lam| * l2Form N i T ((sliceIdSystem N i T).H (bddEmb N i T f)) (bddEmb N i T f) ≤ _
  rw [hH, hnorm f hfm hfb]
  have h1 := h f hfm hfb hfφ
  have e : |lam| * (1 - κ) * ∫ x, f x ^ 2 ∂(hS i T N)
      = |lam| * ∫ x, f x ^ 2 ∂(hS i T N) - κ * |lam| * ∫ x, f x ^ 2 ∂(hS i T N) := by ring
  linarith

/-- **The per-side Rayleigh bound with the window clauses** (the form `WindowCertificate` is equivalent to):
eventually in `β`, `m′ > 0` and a window `k` with `C ≤ 2^k m′ ≤ 2C` past the crossover, such that at every
power-of-two side `n ≥ 2^k` and direction the slice transfer has a top pair with
`Q(f) ≤ |λ| (1 − κ₀ m′) ∫ f²` on bounded measurable `f ⊥ φ`. DERIVED: `2` the doubling and the gauge group. -/
def WindowRayleigh (C κ₀ : ℝ) : Prop :=
  ∀ᶠ β in atTop, 0 < mprime (M := 2) two_ne_zero β ∧ ∃ k : ℕ,
    C ≤ (2 : ℝ) ^ k * mprime (M := 2) two_ne_zero β ∧
    (2 : ℝ) ^ k * mprime (M := 2) two_ne_zero β ≤ 2 * C ∧ PastPeak β k ∧
    ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ^ k ≤ n → ∀ i : Fin 4,
      ∃ lam : ℝ, ∃ φ : Cfg i (CentreSectorSeed.Tr n i) 2 → ℝ,
        TopPair 2 i (CentreSectorSeed.Tr n i) β lam φ ∧
        ∀ f : Cfg i (CentreSectorSeed.Tr n i) 2 → ℝ, Measurable f → (∃ B : ℝ, ∀ z, |f z| ≤ B) →
          ∫ z, f z * φ z ∂(hS i (CentreSectorSeed.Tr n i) 2) = 0 →
          relayForm 2 i (CentreSectorSeed.Tr n i) β f
            ≤ |lam| * (1 - κ₀ * mprime (M := 2) two_ne_zero β)
              * ∫ z, f z ^ 2 ∂(hS i (CentreSectorSeed.Tr n i) 2)

/-- **The per-side Rayleigh bound gives the window certificate** (the identity system at every side), at every
`c₀ ≤ γ ≤ 1`. DERIVED: `1`. -/
theorem windowCertificate_of_rayleigh {C κ₀ γ c₀ : ℝ} (hγ : γ ≤ 1) (hc : c₀ ≤ γ)
    (h : WindowRayleigh C κ₀) : WindowCertificate C κ₀ γ c₀ := by
  filter_upwards [h] with β hβ
  obtain ⟨hm, k, h1, h2, hp, hs⟩ := hβ
  refine ⟨hm, k, h1, h2, hp, fun n hn hkn i => ?_⟩
  obtain ⟨lam, φ, htop, hray⟩ := hs n hn hkn i
  have hM : 1 ≤ blockTerms (2 ^ k) := by unfold blockTerms; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact ⟨lam, φ, sliceIdSystem 2 i (CentreSectorSeed.Tr n i), htop, sliceCompare_idSystem hray,
    blockCert_idSystem hM hγ hc⟩

/-- **The window certificate gives the per-side Rayleigh bound at `κ₀ c₀`.** DERIVED: no numeral. -/
theorem windowRayleigh_of_windowCertificate {C κ₀ γ c₀ : ℝ} (hκ : 0 ≤ κ₀)
    (hW : WindowCertificate C κ₀ γ c₀) : WindowRayleigh C (κ₀ * c₀) := by
  filter_upwards [hW] with β hβ
  obtain ⟨hm, k, h1, h2, hp, h⟩ := hβ
  refine ⟨hm, k, h1, h2, hp, fun n hn hkn i => ?_⟩
  obtain ⟨lam, φ, S, htop, hcmp, hB⟩ := h n hn hkn i
  refine ⟨lam, φ, htop, fun f hfm hfb hfφ => ?_⟩
  have := relayForm_le_of_blockCert hB hcmp (mul_nonneg hκ hm.le) hfm hfb hfφ
  have e : κ₀ * c₀ * mprime (M := 2) two_ne_zero β = κ₀ * mprime (M := 2) two_ne_zero β * c₀ := by ring
  rw [e]; exact this

/-- **The equivalence**: at `γ = c₀ = 1` and `κ₀ ≥ 0`, the window certificate is the per-side Rayleigh bound.
DERIVED: `1`. -/
theorem windowCertificate_iff_rayleigh {C κ₀ : ℝ} (hκ : 0 ≤ κ₀) :
    WindowCertificate C κ₀ 1 1 ↔ WindowRayleigh C κ₀ := by
  constructor
  · intro h
    have := windowRayleigh_of_windowCertificate hκ h
    rwa [mul_one] at this
  · exact windowCertificate_of_rayleigh le_rfl le_rfl

end Identity

/-! ## 5. Tests -/

section Tests

variable {N : ℕ} [NeZero N] {i : Fin 4} {T : {k : Fin 4 // k ≠ i} → ℕ}

/-- **Strong coupling at a block slice**: at `0 ≤ β ≤ β₀(T)` the per-slice gap `strong_gap_half` is the leg's
conclusion at `x = 1/2`. DERIVED: `1/2` the strong-coupling rate. -/
theorem strong_block_rate {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ StrongTransferGap.betaStrong i T) :
    ∃ lam : ℝ, ∃ φ : Cfg i T N → ℝ, ∃ ρ : ℝ, TransferGapAt N i T β lam φ ρ ∧ ρ ≤ |lam| * (1 - 1 / 2) := by
  obtain ⟨lam, φ, h, -, -⟩ := StrongTransferGap.strong_gap_half (N := N) (i := i) (T := T) hβ hβ0
  exact ⟨lam, φ, |lam| / 2, h, by ring_nf; exact le_rfl⟩

/-- **Strong coupling at every side**: the uniform relay gap is the conclusion a certificate would give, at one
`β₀ > 0` and one rate `e^{−m}`, at every direction and aperture (`UniformRelayStrong.uniformRelayGap`).
DERIVED: `0`. -/
theorem strong_every_side : ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ m : ℝ, 0 < m ∧ ∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
    ∀ (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ), ∃ lam : ℝ, ∃ φ : Cfg i T N → ℝ,
      TransferGapAt N i T β lam φ (|lam| * Real.exp (-m)) :=
  UniformRelayStrong.uniformRelayGap (N := N)

/-- **The per-slice Doeblin threshold falls with the slice**: at every `β > 0` there is a cubic aperture `m` with
`β₀(m) < β`. A per-slice gap at one side does not by itself carry to larger sides.
DERIVED: `3` the transverse dimension; `30` the plaquette count per transverse site; `2`, `1` from `β₀`. -/
theorem betaStrong_lt {β : ℝ} (hβ : 0 < β) :
    ∃ m : ℕ, StrongTransferGap.betaStrong i (fun _ => m) < β := by
  obtain ⟨m, hm⟩ := exists_nat_gt (Real.log (3 / 2) / β)
  refine ⟨m, ?_⟩
  have hcard : (Fintype.card (TT i (fun _ : {k : Fin 4 // k ≠ i} => m)) : ℝ) = (m : ℝ) ^ 3 := by
    simp only [TT, Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ,
      StrongTransferGap.card_ne]
    push_cast; ring
  have hl : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hm0 : (0 : ℝ) < m := lt_trans (div_pos hl hβ) hm
  have hm1 : (1 : ℝ) ≤ m := by
    have : 0 < m := by exact_mod_cast hm0
    exact_mod_cast this
  have hmm : (1 : ℝ) ≤ (m : ℝ) * m := by nlinarith
  have hm3 : (m : ℝ) ≤ (m : ℝ) ^ 3 := by
    calc (m : ℝ) = m * 1 := (mul_one _).symm
      _ ≤ m * (m * m) := mul_le_mul_of_nonneg_left hmm hm0.le
      _ = (m : ℝ) ^ 3 := by ring
  unfold StrongTransferGap.betaStrong
  rw [StrongTransferGap.slabM_eq, hcard]
  have hden : 0 < 2 * (30 * (m : ℝ) ^ 3 + 1) := by positivity
  rw [div_lt_iff₀ hden]
  have h1 : Real.log (3 / 2) < β * m := by
    rw [div_lt_iff₀ hβ] at hm; linarith
  nlinarith

/-- **`β = 0`**: the top pair `(1, 1)` has remainder `0`, so the leg's conclusion holds at every `x ≤ 1`, and the
zoom is past the crossover at every window (`WindowRelay.pastPeak_zero_coupling`). DERIVED: `0`, `1`. -/
theorem zero_coupling_block {x : ℝ} (hx : x ≤ 1) (k : ℕ) :
    TopPair N i T 0 1 (fun _ => 1) ∧
      (∃ ρ : ℝ, TransferGapAt N i T 0 1 (fun _ => 1) ρ ∧ ρ ≤ |(1 : ℝ)| * (1 - x)) ∧ PastPeak 0 k := by
  have h := transferGapAt_zero_coupling (N := N) (i := i) (T := T)
  refine ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩, ⟨0, h, ?_⟩, pastPeak_zero_coupling k⟩
  rw [abs_one, one_mul]; linarith

end Tests

end MassGap.KnabeWindow

end

#print axioms MassGap.KnabeWindow.PatchSystem'.H_selfAdj
#print axioms MassGap.KnabeWindow.PatchSystem'.formH_symm
#print axioms MassGap.KnabeWindow.PatchSystem'.sq_le_of_quad
#print axioms MassGap.KnabeWindow.PatchSystem'.formH_sq_le
#print axioms MassGap.KnabeWindow.PatchSystem'.poincare_on_range
#print axioms MassGap.KnabeWindow.globalGap_of_blockCert
#print axioms MassGap.KnabeWindow.uniform_globalGap
#print axioms MassGap.KnabeWindow.knabeConst_nonpos
#print axioms MassGap.KnabeWindow.relayForm_le_of_compare
#print axioms MassGap.KnabeWindow.relayForm_le_of_blockCert
#print axioms MassGap.KnabeWindow.vacuity_zero_H
#print axioms MassGap.KnabeWindow.side_ge_block
#print axioms MassGap.KnabeWindow.globalGap_of_windowCertificate
#print axioms MassGap.KnabeWindow.rayleigh_of_windowCertificate
#print axioms MassGap.KnabeWindow.transferGapMeasured_of_windowCertificate
#print axioms MassGap.KnabeWindow.strong_block_rate
#print axioms MassGap.KnabeWindow.strong_every_side
#print axioms MassGap.KnabeWindow.betaStrong_lt
#print axioms MassGap.KnabeWindow.zero_coupling_block
#print axioms MassGap.KnabeWindow.idSystem
#print axioms MassGap.KnabeWindow.idSystem_H
#print axioms MassGap.KnabeWindow.blockCert_idSystem
#print axioms MassGap.KnabeWindow.bddSub
#print axioms MassGap.KnabeWindow.integrable_bddSub
#print axioms MassGap.KnabeWindow.l2Form
#print axioms MassGap.KnabeWindow.l2Form_symm
#print axioms MassGap.KnabeWindow.l2Form_nonneg
#print axioms MassGap.KnabeWindow.bddEmb
#print axioms MassGap.KnabeWindow.bddEmb_apply
#print axioms MassGap.KnabeWindow.sliceCompare_idSystem
#print axioms MassGap.KnabeWindow.windowCertificate_of_rayleigh
#print axioms MassGap.KnabeWindow.windowRayleigh_of_windowCertificate
#print axioms MassGap.KnabeWindow.windowCertificate_iff_rayleigh
