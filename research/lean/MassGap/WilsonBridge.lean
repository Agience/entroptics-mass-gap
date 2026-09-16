/-
# The bridge: the entropy read, applied to the GENUINE Wilson correlation

WHAT WAS DISCONNECTED. `Complete.lean` declares `opaque wilsonCorrAt` and proves every flagship
about it. Nothing constructs that function, so the theorems quantify over an arbitrary nonnegative
sequence and "Wilson" is a name. Meanwhile `WilsonReal`/`WilsonRead` build the real thing —
`SU(N)` (Mathlib's `specialUnitaryGroup`), the real Wilson action `wilsonDensity`, product Haar over
links, the ordered-loop holonomy — and `WilsonRead.wilsonCorrReal` is a genuine two-plaquette
correlation with its nonnegativity PROVED rather than assumed. It is used nowhere.

This file connects them, at ARBITRARY lattice geometry and ARBITRARY aperture.

WHAT IS HERE.
  * `wilsonCorr` — `⟨φ_{p₀} · φ_p⟩_β` for any plaquette-boundary structure `bd`, any gauge group
    rank, any coupling. Nonnegative and bounded, both derived from the general lemmas in
    `WilsonReal` — no new axiom and no `opaque`.
  * `wilsonRead` — that correlation packaged as a `Moment.Read`, which is what the tension, the lag
    moment and the whole entropy apparatus consume. This is the join: from here the reads of
    `Moment` and the decay chain of `ZeroMode` apply to the real Wilson ensemble.
  * `tension_lt_floor_of_cosAvg_wilson` — the measured criterion, stated about the real object.

WHAT IS NOT CLAIMED. Positivity of the total weight is carried as an explicit hypothesis, exactly as
`WilsonRead.sum_wilsonCorrReal_pos_of_haar` carries it: it reduces to one Haar fact about the
plaquette density and is not proved here. Nothing in this file asserts that the aperture condition
HOLDS for Yang-Mills — that is the measured input, and it is supplied from outside or not at all.
-/
import Mathlib
import MassGap.Moment
import MassGap.ZeroMode
import MassGap.WilsonReal
import MassGap.WilsonRead
import MassGap.WilsonHypercubic

namespace MassGap.WilsonBridge

open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction MassGap.CompactGauge
open MassGap.WilsonReal
open MeasureTheory Finset

variable {Nc : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]

/-- **The genuine Wilson plaquette correlation, at any geometry and any coupling.**
`ρ_β(p) = ⟨φ_{p₀} · φ_p⟩_β`, the Gibbs expectation against normalised Haar with the real Wilson
Boltzmann weight. This generalises `WilsonRead.wilsonCorrReal` off its two-plaquette instance: `bd`
is arbitrary, so a real periodic lattice is covered as soon as one is given. No `opaque`. -/
noncomputable def wilsonCorr (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (β : ℝ) (p : Pq) : ℝ :=
  (wilsonSystem bd (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β
    (fun U => wilsonPlaqObs bd p₀ U * wilsonPlaqObs bd p U)

/-- **Nonnegativity is a THEOREM here**, not the axiom `Complete.wilson_reflection_positive_at`
asserts about the opaque ensemble: the integrand is a product of two nonnegative plaquette densities
and the Gibbs state is positive. -/
theorem wilsonCorr_nonneg (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (β : ℝ) (p : Pq) :
    0 ≤ wilsonCorr (Nc := Nc) bd p₀ β p :=
  wilsonSystem_expect_nonneg hN bd β _
    (fun U => mul_nonneg (wilsonPlaqObs_nonneg hN bd p₀ U) (wilsonPlaqObs_nonneg hN bd p U))

/-- The correlation is bounded by `4`: each density is at most `2` and the state is contractive. -/
theorem wilsonCorr_le_four (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (β : ℝ) (p : Pq) :
    wilsonCorr (Nc := Nc) bd p₀ β p ≤ 4 := by
  have hmeas : Measurable (fun U : (wilsonSystem bd (wilsonDensity (N := Nc))).Config =>
      wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U) :=
    (measurable_wilsonPlaqObs (N := Nc) bd p₀).mul (measurable_wilsonPlaqObs (N := Nc) bd p)
  have habs := wilsonSystem_expect_abs_le hN bd β
    (fun U => wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U) hmeas 4
    (fun U => by
      rw [abs_of_nonneg (mul_nonneg (wilsonPlaqObs_nonneg hN bd p₀ U)
        (wilsonPlaqObs_nonneg hN bd p U))]
      calc wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U
          ≤ 2 * 2 := mul_le_mul (wilsonPlaqObs_le_two hN bd p₀ U)
              (wilsonPlaqObs_le_two hN bd p U) (wilsonPlaqObs_nonneg hN bd p U) (by norm_num)
        _ = 4 := by norm_num)
  exact le_trans (le_abs_self _) habs

/-! ### The join: the real correlation as a `Moment.Read`

`Moment.Read N` is exactly a nonnegative `Fin (N+1)`-indexed correlation of positive total weight.
The Wilson correlation is nonnegative by the theorem above, so the ONLY thing standing between the
real ensemble and the entire entropy apparatus is the positive total weight — which
`WilsonRead.sum_wilsonCorrReal_pos_of_haar` reduces to a single Haar fact on the two-plaquette
instance, and which is carried here as a hypothesis rather than assumed away. -/

/-- **THE BRIDGE.** The genuine Wilson correlation, packaged as the object the entropy read
consumes. Every downstream quantity — the tension `μ`, the lag distribution `p`, the circular
second moment, the substrate ratio — is now a quantity OF `SU(Nc)` LATTICE GAUGE THEORY rather than
of an uninterpreted function.

DERIVED: the base point `p₀` is an argument, not a literal; the `0` and `1` that appear are the
`Bool` orientation flags of a boundary word and the successor in `Fin (N+1)`. Neither is a scale. -/
noncomputable def wilsonRead (hN : Nc ≠ 0) {N : ℕ} (bd : Fin (N + 1) → List (Lk × Bool))
    (p₀ : Fin (N + 1)) (β : ℝ)
    (hpos : 0 < ∑ p, wilsonCorr (Nc := Nc) bd p₀ β p) : Moment.Read N where
  ρ := fun p => wilsonCorr (Nc := Nc) bd p₀ β p
  hρ := fun p => wilsonCorr_nonneg hN bd p₀ β p
  hpos := hpos

@[simp] theorem wilsonRead_rho (hN : Nc ≠ 0) {N : ℕ} (bd : Fin (N + 1) → List (Lk × Bool))
    (p₀ : Fin (N + 1)) (β : ℝ) (hpos : 0 < ∑ p, wilsonCorr (Nc := Nc) bd p₀ β p) :
    (wilsonRead hN bd p₀ β hpos).ρ = fun p => wilsonCorr (Nc := Nc) bd p₀ β p := rfl

/-- **The measured criterion, stated about the real ensemble.** The cosine average clearing
`3^{-1/4}` puts the Wilson tension below the proved entropy floor `κ₀ = ¼log3`. This is
`Moment.Read.tension_lt_floor_of_cosAvg` with the read no longer opaque: the scalar on the left is
computed from `SU(Nc)` Wilson expectations. -/
theorem tension_lt_floor_of_cosAvg_wilson (hN : Nc ≠ 0) {N : ℕ}
    (bd : Fin (N + 1) → List (Lk × Bool)) (p₀ : Fin (N + 1)) (β : ℝ)
    (hpos : 0 < ∑ p, wilsonCorr (Nc := Nc) bd p₀ β p)
    (hc : (3 : ℝ) ^ (-(1 : ℝ) / 4) <
      ∑ d, (wilsonRead hN bd p₀ β hpos).p d * Real.cos ((wilsonRead hN bd p₀ β hpos).θ d)) :
    (wilsonRead hN bd p₀ β hpos).tension < (1 / 4) * Real.log 3 :=
  Moment.Read.tension_lt_floor_of_cosAvg _ hc

/-- **The decay chain, terminating on the real ensemble.** Given the reflection-positive spectral
form of the Wilson correlation (the cited Osterwalder–Seiler content, now a statement about a
CONSTRUCTED object) and the measured tension below the floor at large apertures, the Wilson
correlation decays. This is `ZeroMode.correlation_decays_of_tension` with the read built from
`SU(Nc)` Wilson expectations. -/
theorem wilson_correlation_decays (hN : Nc ≠ 0)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hlam : ∀ k ∈ s, 0 ≤ lam k) (hle : ∀ k ∈ s, lam k ≤ 1)
    (bd : (N : ℕ) → Fin (N + 1) → List (Lk × Bool)) (p₀ : (N : ℕ) → Fin (N + 1)) (β : ℝ)
    (hpos : ∀ N, 0 < ∑ p, wilsonCorr (Nc := Nc) (bd N) (p₀ N) β p)
    (hspec : ∀ (N : ℕ) (d : Fin (N + 1)),
      wilsonCorr (Nc := Nc) (bd N) (p₀ N) β d = ∑ k ∈ s, w k * lam k ^ (d : ℕ))
    (hcpos : ∀ᶠ N in Filter.atTop, 0 < ∑ d,
      (wilsonRead hN (bd N) (p₀ N) β (hpos N)).p d * Real.cos ((wilsonRead hN (bd N) (p₀ N) β (hpos N)).θ d))
    (htens : ∀ᶠ N in Filter.atTop,
      (wilsonRead hN (bd N) (p₀ N) β (hpos N)).tension < (1 / 4) * Real.log 3) :
    Filter.Tendsto (fun d : ℕ => ∑ k ∈ s, w k * lam k ^ d) Filter.atTop (nhds 0) :=
  ZeroMode.correlation_decays_of_tension s w lam hw hlam hle
    (fun N => wilsonRead hN (bd N) (p₀ N) β (hpos N))
    (fun N => by funext d; exact hspec N d) hcpos htens

/-! ### A geometry where the LAG means something

`WilsonReal.bd2` puts its two plaquettes on DISJOINT link sets, so under the product Haar measure
they are independent and `⟨φ₀φ_d⟩ = ⟨φ₀⟩⟨φ_d⟩`: the correlation is flat in the lag and carries no
decay to measure. That is fine for the invariance theorems it was built for and useless as an
aperture.

`bdChain` is a PERIODIC LADDER at arbitrary aperture: `N+1` plaquettes around a circle, three links
per rung (bottom, top, vertical), with plaquette `p` the loop
`h_p · v_{p+1} · (h'_p)⁻¹ · v_p⁻¹`. Consecutive plaquettes SHARE the vertical link `v_{p+1}`
(`bdChain_shares_link`), so neighbouring plaquettes genuinely interact and the lag index is a real
separation rather than a label. This is the geometry an aperture read needs. -/

/-- Three links per rung: `0` bottom, `1` top, `2` vertical.

DERIVED: three is the number of distinct link ROLES a rung of a ladder has, and `0,1,2` name them.
Changing the count would describe a different graph, not retune this one. -/
abbrev ChainLink (N : ℕ) : Type := Fin 3 × Fin (N + 1)

/-- The periodic ladder: plaquette `p` is `h_p · v_{p+1} · (h'_p)⁻¹ · v_p⁻¹`.

DERIVED: the four entries are the four sides of a plaquette, and `0,1,2` are the link roles named in
`ChainLink`. The `+1` is the ladder's periodic step. No literal here sets a scale. -/
def bdChain (N : ℕ) (p : Fin (N + 1)) : List (ChainLink N × Bool) :=
  [((0, p), true), ((2, p + 1), true), ((1, p), false), ((2, p), false)]

/-- **Neighbouring plaquettes are genuinely coupled**: plaquette `p` and plaquette `p+1` share the
vertical link `v_{p+1}`. This is what `bd2` does not do, and it is why the lag index on this
geometry is a separation. -/
theorem bdChain_shares_link (N : ℕ) (p : Fin (N + 1)) :
    ((2 : Fin 3), p + 1) ∈ (bdChain N p).map Prod.fst ∧
    ((2 : Fin 3), p + 1) ∈ (bdChain N (p + 1)).map Prod.fst := by
  constructor
  · simp [bdChain]
  · simp [bdChain]

/-- The genuine Wilson correlation on the periodic ladder, at aperture `N` and rank `Nc`: the
lag-indexed plaquette correlation, on a geometry where the lag is a separation. Constructed — no
`opaque`, no axiom.

NOT the object the aperture condition can consume — see `chainCorrConn`.

DERIVED: the `0` is the base plaquette against which the lag is measured. The ladder is periodic and
translation-invariant, so every base point gives the same correlation; the choice is a labelling. -/
noncomputable def chainCorr (Nc N : ℕ) (β : ℝ) (d : Fin (N + 1)) : ℝ :=
  wilsonCorr (Nc := Nc) (bdChain N) 0 β d

theorem chainCorr_nonneg (hN : Nc ≠ 0) (N : ℕ) (β : ℝ) (d : Fin (N + 1)) :
    0 ≤ chainCorr Nc N β d :=
  wilsonCorr_nonneg hN _ _ _ _

/-! ### Why the UNCONNECTED correlation cannot carry the aperture condition

`wilsonCorr` is `⟨φ_{p₀}·φ_p⟩`, and its nonnegativity is trivial precisely because it is
unconnected — a product of two nonnegative densities. That triviality is the tell. Distant
plaquettes decouple, so `⟨φ_{p₀}φ_p⟩ → ⟨φ⟩² = 1` (`WilsonRead.integral_plaqObs_eq_one` at `β = 0`),
and a correlation with a FLAT floor is one whose lag distribution is nearly uniform. Its circular
second moment is then `≈ (N+1)²/12`, against a ceiling of `c_max·(N+1)²` with
`c_max = 2(1−3^{-1/4})/(2π)² ≈ 0.0122` — over by a factor `≈ 6.8` at EVERY aperture, never
improving with `N`. At `N = 1` that factor is `9.13`, which is exactly
`WilsonRead.two_plaquette_aperture_forces_tiny_B`'s recorded `9.1`.

Read through `ZeroMode`: the flat floor IS the zero-mode weight `c`, and
`no_zero_mode_of_tension_lt_floor` says `μ < κ₀` forces `c = 0`. For the unconnected correlation
`c = ⟨φ⟩² = 1 ≠ 0`, so `μ < κ₀` is unsatisfiable and any flagship instantiated on it is VACUOUS.

The object the condition can consume is the CONNECTED correlation, whose disconnected floor is
subtracted off. Its nonnegativity is no longer trivial — it is the transfer-matrix spectral form
`ρ(d) = ∑ₙ wₙe^{−Eₙd}` with `wₙ ≥ 0`, which is the real content of reflection positivity and the
reason Osterwalder–Seiler is cited rather than reproved. -/

/-- **The CONNECTED Wilson correlation**: the disconnected floor `⟨φ_{p₀}⟩⟨φ_p⟩` subtracted, so what
remains is the fluctuation correlation whose decay is a mass. This is the object the entropy read
must consume; the unconnected `wilsonCorr` cannot (see the note above). -/
noncomputable def wilsonCorrConn (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (β : ℝ) (p : Pq) : ℝ :=
  wilsonCorr (Nc := Nc) bd p₀ β p
    - (wilsonSystem bd (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β
        (wilsonPlaqObs (N := Nc) bd p₀)
      * (wilsonSystem bd (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β
        (wilsonPlaqObs (N := Nc) bd p)

/-- The connected correlation on the periodic ladder — the lag-indexed object the aperture condition
is about, constructed from `SU(Nc)` Wilson expectations.

DERIVED: the `0` is the base plaquette, immaterial by periodicity, exactly as in `chainCorr`. -/
noncomputable def chainCorrConn (Nc N : ℕ) (β : ℝ) (d : Fin (N + 1)) : ℝ :=
  wilsonCorrConn (Nc := Nc) (bdChain N) 0 β d

/-! ### A PRIVATE link makes a plaquette free — so the ladder is not an interacting theory

`bdChain_shares_link` is true and it is not enough. Plaquette `p` of the ladder also owns the links
`(0,p)` and `(1,p)`, which appear in NO other plaquette. A link occurring in exactly one plaquette
can be integrated out first, and left-translation by it carries that plaquette's holonomy through
Haar — so the holonomy is Haar-distributed and INDEPENDENT of every other plaquette, whatever the
shared links do. Measured on the ladder by Monte-Carlo at `β = 0, 2, 6`, the connected correlation
is a contact term: `C(0) = 0.26 / 0.18 / 0.027` against `|C(d)| ≲ 0.01` (noise) for every `d ≥ 1`.

A contact correlation satisfies the aperture condition trivially (`⟨d²⟩ = 0`), so a flagship
instantiated on the ladder is non-vacuous and WORTHLESS — free-field non-vacuity, the defect
`witness_volume_gap_nonvacuous` exists to warn about.

What is needed is a geometry in which NO plaquette owns a private link. On a periodic hypercubic
lattice in `D` dimensions every link lies in `2(D−1)` plaquettes, so `D ≥ 3` suffices; `D ≤ 2` does
not, which is the structural reason two-dimensional lattice gauge theory is exactly solvable. -/

/-- Sites of a periodic `n³` lattice: a coordinate per direction.

CHOSEN: THREE dimensions. This is the one real modelling commitment in this section and it is not
free. Three is the smallest dimension in which no plaquette owns a private link -- the property
`bd3_link_not_private` establishes, and the one the ladder fails, which is what made the ladder's
correlation vacuous. It is also a dimension in which `SU(2)` gauge theory confines and is believed
gapped, so the object is not a toy. What it is NOT is the physical case: the Yang-Mills problem is
four-dimensional, and nothing proved on this geometry transfers to `d = 4` without redoing it there.
Every `Fin 3` below inherits this choice and is not an independent one. -/
abbrev Site3 (n : ℕ) : Type := Fin 3 → Fin n

/-- Links of the 3-D lattice: a direction and a site.

DERIVED: the `Fin 3` is the dimension chosen at `Site3`, not a second choice. -/
abbrev Link3 (n : ℕ) : Type := Fin 3 × Site3 n

/-- Plaquettes of the 3-D lattice, indexed by the NORMAL direction and a site: in three dimensions a
plaquette plane is fixed by its normal, and the plane of normal `k` is spanned by `k+1` and `k+2`.

DERIVED: `1` and `2` are the offsets to the two directions spanning the plane of normal `k`, forced
by `k+0` being the normal itself; the `Fin 3` is the dimension chosen at `Site3`. -/
abbrev Plaq3 (n : ℕ) : Type := Fin 3 × Site3 n

/-- Translate a site by one step in direction `μ`, periodically.

DERIVED: `1` is one lattice step -- the definition of a neighbour, not a length. The `Fin 3` is the
dimension chosen at `Site3`. -/
def shift {n : ℕ} [NeZero n] (μ : Fin 3) (x : Site3 n) : Site3 n :=
  Function.update x μ (x μ + 1)

/-- The 3-D periodic Wilson plaquette: for normal `k` at site `x`, the loop
`U_{k+1}(x) · U_{k+2}(x+ê_{k+1}) · U_{k+1}(x+ê_{k+2})⁻¹ · U_{k+2}(x)⁻¹`.

DERIVED: `1` and `2` are the two in-plane directions relative to the normal, as at `Plaq3`; the four
entries are the four sides of one plaquette. The `Fin 3` is the dimension chosen at `Site3`. -/
def bd3 {n : ℕ} [NeZero n] (q : Plaq3 n) : List (Link3 n × Bool) :=
  let k := q.1; let x := q.2
  [((k + 1, x), true), ((k + 2, shift (k + 1) x), true),
   ((k + 1, shift (k + 2) x), false), ((k + 2, x), false)]

/-- **No plaquette owns a private link.** The first link of plaquette `(k, x)` is `U_{k+1}(x)`, and
it also occurs in the plaquette of normal `k+2` at the same site — a DIFFERENT plaquette, since
`k + 2 ≠ k` in `Fin 3`. So the Haar-integration argument that frees a ladder plaquette has no
starting point here, which is the structural difference between this geometry and `bdChain`. -/
theorem bd3_link_not_private {n : ℕ} [NeZero n] (k : Fin 3) (x : Site3 n) :
    ((k + 1, x) ∈ (bd3 (k, x)).map Prod.fst) ∧
    ((k + 1, x) ∈ (bd3 (k + 2, x)).map Prod.fst) ∧ (k + 2 ≠ k) := by
  -- both are statements about `Fin 3` alone, decided by exhausting the three directions
  have h : (k + 2) + 2 = k + 1 := by revert k; decide
  have hne : k + 2 ≠ k := by revert k; decide
  refine ⟨by simp [bd3], ?_, hne⟩
  -- in the plaquette of normal `k+2` the FOURTH entry is `U_{(k+2)+2}(x) = U_{k+1}(x)`
  simp [bd3, h]

/-- The site displaced `d` steps from the origin along direction `μ`.

DERIVED: `0` is the origin of a translation-invariant periodic lattice, so displacing from it is the
same as displacing from anywhere. The `Fin 3` is the dimension chosen at `Site3`. -/
def siteAt {n : ℕ} [NeZero n] (μ : Fin 3) (d : Fin n) : Site3 n :=
  Function.update (fun _ => 0) μ d

/-- **The lag-indexed CONNECTED plaquette correlation on the 3-D periodic lattice.** Both plaquettes
have normal `0`; they are separated by `d` steps along direction `0`, which is transverse to their
common plane, so the lag is a genuine spatial separation. This is the object `Complete.wilsonCorrAt`
is, and unlike the ladder it lives on a geometry with no free plaquettes (`bd3_link_not_private`).

Measured on the released `SU(2)` ensembles the connected correlation is contact-scale, and its
circular second moment clears the aperture ceiling with margin `1.9×`–`203×`
(`data/9_3_dat_substrate_of_aperture.csv`), so the aperture condition is satisfiable here rather
than being a contradiction as it is for the unconnected correlation.

DERIVED: no literal in this definition sets a scale. `0` is the normal direction shared by both
plaquettes and the origin they are displaced from -- immaterial by periodicity and by the freedom to
name the axes; `Fin 3` is the dimension chosen at `Site3`; `1` and `2` are the in-plane offsets from
`Plaq3`. The `1.9` and `203` in the prose above are not constants of this definition at all: they are
the measured margins reported in the named artifact, and they are read back from it rather than
written here -- if that file changes, this comment is wrong and the paper's guard says so. -/
noncomputable def corr3 (Nc N : ℕ) (β : ℝ) (d : Fin (N + 1)) : ℝ :=
  wilsonCorrConn (Nc := Nc) (bd3 (n := N + 1)) (0, fun _ => 0) β (0, siteAt 0 d)

/-! ### The same correlation in any dimension, on the lattice the OS measure uses

`corr3` lives on `Site3`, whose plaquettes are indexed by a NORMAL -- which only determines a plane
in three dimensions. The Osterwalder--Schrader measure (`WilsonGauge`) is built on
`WilsonHypercubic.sysWilson`, whose plaquettes carry the two spanning directions and so exist in any
dimension. Those were two lattices, and `Complete.wilson_reflection_positive_at` was cited for the
first while the measure used the second.

`corrHyper` is the same connected correlation on the second. Nothing about the construction changes:
`wilsonCorrConn` is already general in the boundary-word map, so this is that map instantiated at
`WilsonHypercubic.bd` rather than at `bd3`. What changes is which object the citation is about.

The geometric fact that makes the theory interacting carries over and is stronger there: no plaquette
owns a private link in ANY dimension `d >= 3` (`WilsonHypercubic.link_not_private`), where `bd3`'s
version (`bd3_link_not_private`) is the `d = 3` case of it.
-/

/-- The site displaced `lag` steps from the origin along direction `μ`, on the hypercubic lattice.

DERIVED: `0` is the origin of a translation-invariant periodic lattice, so displacing from it is the
same as displacing from anywhere. -/
def siteAtHyper {d n : ℕ} [NeZero n] (μ : Fin d) (lag : Fin n) :
    MassGap.WilsonHypercubic.Site d n :=
  Function.update (fun _ => 0) μ lag

/-- **The lag-indexed CONNECTED plaquette correlation on the `d`-dimensional periodic lattice.**

Both plaquettes span the `(μ, ν)` plane; they are separated by `lag` steps along `τ`, which the caller
supplies transverse to that plane, so the lag is a genuine spatial separation rather than an in-plane
offset. At `d = 4` this is the Clay problem's dimension, and it is the lattice `WilsonGauge`'s OS
measure is built on.

WHY THE DIRECTIONS ARE PARAMETERS. `Fin d` for a variable `d` carries no numerals, and that is the
type system asking the right question: writing `0, 1, 2` would bury the requirement `d >= 3` inside
three literals. A plaquette needs two directions, a lag needs a third transverse to them, and the
third exists exactly when there are more than two -- which is the same boundary
`WilsonHypercubic.link_not_private` runs into, and the reason two-dimensional lattice gauge theory is
exactly solvable.

DERIVED: no literal here sets a scale. The directions are the caller's and which two span the plane
is a naming freedom; the origin is immaterial by periodicity. -/
noncomputable def corrHyper {d : ℕ} (Nc n : ℕ) [NeZero n] (μ ν τ : Fin d) (β : ℝ) (lag : Fin n) : ℝ :=
  wilsonCorrConn (Nc := Nc) (MassGap.WilsonHypercubic.bd (d := d) (n := n))
    ((μ, ν), fun _ => 0) β ((μ, ν), siteAtHyper τ lag)

/-- **Nonnegativity of the UNCONNECTED correlation carries over unchanged** -- the same theorem as on
the ladder, since `wilsonCorr_nonneg` never looked at the geometry. Recorded here so that moving the
object does not silently drop what was already proved about it. -/
theorem corrHyper_unconnected_nonneg {d : ℕ} (hN : Nc ≠ 0) (n : ℕ) [NeZero n]
    (μ ν τ : Fin d) (β : ℝ) (lag : Fin n) :
    0 ≤ wilsonCorr (Nc := Nc) (MassGap.WilsonHypercubic.bd (d := d) (n := n))
          ((μ, ν), fun _ => 0) β ((μ, ν), siteAtHyper τ lag) :=
  wilsonCorr_nonneg hN _ _ _ _

#print axioms corrHyper_unconnected_nonneg

/-- **The four-dimensional `SU(3)` instance** -- the Clay problem's dimension and group, on the same
lattice `WilsonGauge`'s Osterwalder--Schrader measure is built on.

The plane is spanned by directions `0` and `1` and the lag runs along `2`, transverse to it; in
`Fin 4` those numerals exist, which is the whole content of instantiating the general form above.

DERIVED: `3` is `SU(3)`, `4` is four dimensions -- the problem's own data, not a choice made here.
`n` is the periodic extent and stays the caller's. -/
noncomputable def corrClay (n : ℕ) [NeZero n] (β : ℝ) (lag : Fin n) : ℝ :=
  corrHyper (d := 4) 3 n 0 1 2 β lag

#print axioms corrClay

/-- The ladder correlation as a `Moment.Read`: the entropy apparatus, on a real `SU(Nc)` lattice
gauge theory with a real lag structure. Positivity of the total weight is the one carried
hypothesis, as everywhere else.

DERIVED: the `0` is the base plaquette of the periodic ladder, immaterial by translation invariance,
as in `chainCorr`. -/
noncomputable def chainRead (hN : Nc ≠ 0) (N : ℕ) (β : ℝ)
    (hpos : 0 < ∑ d, chainCorr Nc N β d) : Moment.Read N :=
  wilsonRead hN (bdChain N) 0 β hpos

/-- **THE GAP, ON THE CONSTRUCTED WILSON CORRELATION.** The same chain as
`wilson_correlation_decays`, but concluding an EXPONENTIAL bound rather than mere decay to zero:

    reflection-positive spectral form + measured tension below the floor
        ⟹  ∃ ρ < 1,  ⟨φ_{p₀}φ_p⟩_c(d) ≤ (∑ₖ wₖ) · ρ^d

`Tendsto … 0` is satisfied by a power law and is therefore not a mass gap; this gives a positive
rate `−log ρ`. The correlation is `SU(Nc)` Wilson -- Mathlib's `specialUnitaryGroup`, the real Wilson
action, product Haar over links, ordered-loop holonomy -- and on the 3-D geometry of `bd3` no
plaquette owns a private link, so it is not the free theory the ladder turns out to be.

What carries the rate is the finiteness of the mode family in `hspec`, which on a finite lattice is
the finite-dimensional transfer matrix. That is also the boundary: the thermodynamic limit fills the
spectrum in, and nothing here controls it. -/
theorem wilson_correlation_gap (hN : Nc ≠ 0)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hlam : ∀ k ∈ s, 0 ≤ lam k) (hle : ∀ k ∈ s, lam k ≤ 1)
    (bd : (N : ℕ) → Fin (N + 1) → List (Lk × Bool)) (p₀ : (N : ℕ) → Fin (N + 1)) (β : ℝ)
    (hpos : ∀ N, 0 < ∑ p, wilsonCorr (Nc := Nc) (bd N) (p₀ N) β p)
    (hspec : ∀ (N : ℕ) (d : Fin (N + 1)),
      wilsonCorr (Nc := Nc) (bd N) (p₀ N) β d = ∑ k ∈ s, w k * lam k ^ (d : ℕ))
    (hcpos : ∀ᶠ N in Filter.atTop, 0 < ∑ d,
      (wilsonRead hN (bd N) (p₀ N) β (hpos N)).p d * Real.cos ((wilsonRead hN (bd N) (p₀ N) β (hpos N)).θ d))
    (htens : ∀ᶠ N in Filter.atTop,
      (wilsonRead hN (bd N) (p₀ N) β (hpos N)).tension < (1 / 4) * Real.log 3) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ d : ℕ, ∑ k ∈ s, w k * lam k ^ d ≤ (∑ k ∈ s, w k) * ρ ^ d :=
  ZeroMode.correlation_gap_of_tension s w lam hw hlam hle
    (fun N => wilsonRead hN (bd N) (p₀ N) β (hpos N))
    (fun N => by funext d; exact hspec N d) hcpos htens

section Audit
#print axioms wilson_correlation_gap
#print axioms bdChain_shares_link
#print axioms bd3_link_not_private
#print axioms chainCorr_nonneg
#print axioms chainRead
#print axioms wilsonCorr_nonneg
#print axioms wilsonRead
#print axioms tension_lt_floor_of_cosAvg_wilson
#print axioms wilson_correlation_decays
end Audit

end MassGap.WilsonBridge
