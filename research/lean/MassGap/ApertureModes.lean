import Mathlib
import MassGap.ZoomFree

/-!
# MassGap.ApertureModes — the observer reads only its aperture, through a measured number of modes

The author: "An observer can only ever see what is inside the aperture." and "the observer does not choose
the aperture; the signal sets its own diffraction limit". `ZoomFree.ApertureSettles` reads the channel through
`M` existential modes, and `ZoomFree.apertureSettlesAt_iff_one` shows that such a count is no constraint: one
mode, the reading itself, always serves. This module states the mechanism in three separate layers, with
the count measured from the field, as the entroptics library measures it: the screen is connected, so the
matching read is the centred one, `entroptics.reads.axis_spectrum` (the correlation eigenvalues of the
screen after `_centred`) read through `_fill_of` by `phi_T` / `phi_F` (`entroptics/src/entroptics/reads.py`,
lines ~378–427), the fill fraction `2^H / n`; the count is `n · phi_T = 2^H`, here in nats, `exp H`. On a
translation-invariant screen the Gram's diagonal is constant, so the correlation spectrum normalized is the
Gram's. `entroptics.reads.phi` (lines ~97–138) reads the raw block uncentred and is not this read. On a
spectrum with no power `_fill_of` returns NaN and `spDim` returns `1`.

The count in this module's own mechanism is decorative. Since `apDim ≥ 1` (`spDim` of a spectrum is at least
`1` on a nonnegative spectrum, argued: the entropy is nonnegative), `ApertureModesAt` is
`ZoomFree.ApertureOneAt` up to constants together with an unrelated bound on `apDim`: its moment clauses
give `ApertureOneAt`'s at `max(D, 1)` times the noise (`apertureOneAt_of_modes`), and `ApertureOneAt`'s
give them back with the factor `apDim^{2p} ≥ 1` to spare (argued). The
formulation in which the count does the work is `ApertureCount`: there the hypotheses bound each mode
relative to its own variance and the reading's variance alone, and the count converts that one second moment
into every even moment.
Declarations are in the namespace `MassGap.ApertureModes`.

## 1. Aperture locality (proved)

* `ReadsOn A F`: `F` is a function of the configuration on the link set `A` only (two configurations equal on
  `A` give equal readings): the observable is measurable with respect to the σ-algebra of the links of `A`.
* `aperture Wf k s j`: the links within the flow's lattice range `(Wf s).range k` of the support
  `chanSupp j` of the channel field `mField j` (`ConfFlow.local_V`, the flow's light cone at step `k`).
* `msFlow_readsOn`: the observer's reading `msFlow Wf k s j` reads on its aperture
  (`ContinuumFlow.isLocalOn_comp`). `msFlow_factors`: it factors through the restriction of the
  configuration to the aperture. Nothing outside the aperture enters any reading; this layer carries no
  moment bound.

## 2. The measured number of modes (defined)

* `screen Wf k s j`: the channel reading at the sites `y ∈ {0, …, L − 1}⁴` of the aperture box, `L = ⌈s/a_k⌉`
  lattice steps per side (the side `s` of the aperture, in lattice units), each by lattice translation
  (`ContinuumField.transObs`).
* `gram ν F`: the Gram (covariance) matrix `ν(Fₓ F_y)` of a screen under a state (`gram_isHermitian`); the
  screen is connected (`msFlow` subtracts the state mean), so it is the connected correlation of
  `entroptics.reads.axis_spectrum`.
* `spDim w = exp(−∑ pᵢ log pᵢ)`, `p = w / ∑ w`: the entropy-effective number of modes of a spectrum
  (`exp H` in nats is `2^H` in bits). `spDim_const`: `n` equal modes read `n`; `spDim_single`: one mode reads
  `1`. The count is read from the spectrum and has no witness to choose.
* `apDim Wf k s j = spDim (eigenvalues (gram ν_k (screen Wf k s j)))`: the measured number of modes of the
  observer's reading at aperture `s` and step `k`; `apDim_pos`.

## 3. The mechanism

**`ApertureModesAt b₀ z b Wf`** (and `ApertureModes = ApertureModesAt (b0 N)`): one `u > 0` and noise
exponents `γ`, `γP` with

* (finite information) every channel has one `D` with `apDim Wf k s j ≤ D` at every aperture `s ∈ (0, b]`,
  eventually in the step: the measured number of modes stays bounded, in aperture units, along the zoom;
* (settling per occupied mode) at every aperture and order `2p`, eventually in the step, the reading's even
  moment is within the free Wick count at the canonical size, through `apDim` modes each at the noise
  `σⱼ ḡ²(s)^{κⱼ}` of the aperture's running coupling:
  `ν_k(msFlow^{2p}) ≤ ((2p)!)^{wickIx j} apDim^{2p} (σⱼ ḡ²(s)^{κⱼ} / s^{d_j})^{2p}`;
* (obs) at the observer's own aperture `b`, eventually in the step and at every plaquette, the measured
  number of plaquette modes within one `DP`, the flowed plaquette mean within `E a_k⁴`, and every even moment
  within `(2m)! apDim^{2m} σP^{2m}`;
* (af) the trace kernel settles onto the tree value times `ḡ²(r)²` (as in `ZoomFree`).

The moment bounds are carried by layer 3 (settling); layer 1 carries none. The count bound of layer 2 only
removes the factor `apDim^{2p}` that layer 3 inserts, so it carries no weight of its own (module docstring,
above).

## 4. The derivations (proved)

* `apertureOneAt_of_modes`: `ApertureModesAt` gives `ZoomFree.ApertureOneAt` at noise `max(D, 1) σⱼ` (the
  measured count replaced by its bound); `apertureSettlesAt_of_modes` through
  `ZoomFree.apertureSettlesAt_iff_one`.
* `substrateCoreCL_of_apertureModes`: `ApertureModes z b Wf`, `b > 0`, `Wf b = W` give
  `ClusterRoute.SubstrateCoreCL W z b Wf`.
* `clayStatementOf_of_apertureModes`: the root from `StrongEnd N`, `ScaleLightCone.ZoomSettlesUV` and
  `CoreInputsAlongWAM` (the bundle with the copy of `ApertureModes` in place of `ApertureSettles`).

## 5. The tests

* Not the one-mode form. The count `apDim` is a function of the state and the screen; there is no mode
  family to choose. The one-mode form (`apDim` replaced by `1`, `ZoomFree.ApertureOneAt`) is a different
  statement, and it is not confined to a one-mode spectrum: it bounds the reading's moments directly and can
  hold on a spread spectrum. The two forms agree when the spectrum is one mode (`spDim_single`); on `n`
  equal modes the factor is `n` (`spDim_const`), which loosens `ApertureModesAt`'s moment clause relative to
  `ApertureOneAt`'s rather than tightening it.
* Asymptotic freedom is used for the settling. `tendsto_runG_rpow_zero`: at `b₀ > 0` the per-mode noise
  `ḡ²(s)^{κ}` (`κ > 0`) tends to `0` on zoom-in; `runG_zero_rpow`: at `b₀ = 0` it is the constant `u^κ`, so
  the fields do not settle.
* No gap. Every clause reads at a fixed aperture `s ≤ b` (layer 1: nothing beyond the flow's range enters),
  or the af germ at `0⁺` (`ZoomFree.afSettles_congr`); no clause reads a separation larger than the aperture.
  The free massless field meets layers 2 and 3 with no mass (argued: its flowed screen at `s` has a Gaussian
  spectrum in `s p`, so `exp H` is a fixed number in aperture units, Slepian–Landau–Pollak).
* The rough tail. Layer 3 asks fixed-order moments of the channels, where the floor of
  `BlFamCore.RoughTail` tends to `0` (`ObserverTowerPM.tendsto_roughFloor`), and the exponential moment only
  of the dimension-`4` plaquette class at `b`, as in `ZoomFree` §6; `RoughTail` at `n ≥ 1` refutes no clause
  (argued, as for `ApertureSettles`).
* The band limit with a remainder that vanishes along the zoom is not stated. For any fixed finite family of
  box modes the remainder of the flowed point reading tends, as `k → ∞`, to the continuum out-of-band power
  of the flowed field, which is positive (the heat kernel's spectrum `e^{−2tp²}` has no compact support):
  argued. The finite-information content is therefore stated as the boundedness of the measured count, not
  as an exact projection.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs, the lower ends and the point approached; `1` the floor of the count in
`max(D, 1)`, the one-mode spectrum and the unit observable; `2` the even powers and the square; `4` the
spacetime dimension (the box `{0, …, L − 1}⁴`) and the plaquette dimension; `8` the dimension pair;
`u`, `γ`, `γP`, `σⱼ`, `σP`, `D`, `DP`, `E` existential; `b₀ = b0 N` the theory's one-loop coefficient.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ApertureModes

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
  MassGap.MixConvRP MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll
  MassGap.MultiScaleOS MassGap.ApproxFromExpand MassGap.StrongExpand MassGap.CovFromFlow
  MassGap.SU2Best MassGap.NondegFromProxy MassGap.NonGaussFromScale
  MassGap.ProxyGenObserver MassGap.ProxyBoundFromScale MassGap.ScalePC MassGap.ScalePM
  MassGap.ClusterRoute MassGap.MeasuredSpacing MassGap.ZoomFree

variable {N : ℕ}

/-! ## 1. Aperture locality -/

section Locality

/-- **`F` reads on `A`**: two configurations equal on the links of `A` give the same reading.
DERIVED: no numeral. -/
def ReadsOn (A : Set ILink) (F : C(Cfg N, ℝ)) : Prop :=
  ∀ U U' : Cfg N, (∀ l ∈ A, U l = U' l) → F U = F U'

/-- The links within lattice distance `R` (in every coordinate) of a link of `S`. DERIVED: no numeral. -/
def nearSet (S : Finset ILink) (R : ℕ) : Set ILink :=
  {l' | ∃ l ∈ S, ∀ i, |l'.2 i - l.2 i| ≤ (R : ℤ)}

/-- The support of the channel field `mField j` (a finite set it is local on). DERIVED: no numeral. -/
def chanSupp (j : MIx) : Finset ILink :=
  ((mField j : LField (MassGap.SUN.SU N)).2.1).choose

/-- DERIVED: no numeral. -/
theorem isLocalOn_chanSupp (j : MIx) :
    IsLocalOn (chanSupp (N := N) j) ((mField j : LField (MassGap.SUN.SU N)).1 : Cfg N → ℝ) :=
  ((mField j : LField (MassGap.SUN.SU N)).2.1).choose_spec

/-- **The observer's aperture at scale `s` and step `k`**: the links within the flow's lattice range
`(Wf s).range k` of the channel's support. DERIVED: no numeral. -/
def aperture (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (j : MIx) : Set ILink :=
  nearSet (chanSupp (N := N) j) ((Wf s).range k)

/-- **The observer sees only its aperture**: the flowed reading `msFlow Wf k s j` reads on
`aperture Wf k s j` (the flow's finite range, `ConfFlow.local_V`, composed with the channel's support).
DERIVED: no numeral. -/
theorem msFlow_readsOn [NeZero N] (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (j : MIx) :
    ReadsOn (aperture Wf k s j) (msFlow Wf k s j) := by
  obtain ⟨S', hS', hS'r⟩ := isLocalOn_comp ((Wf s).local_V k) (isLocalOn_chanSupp (N := N) j)
  intro U U' h
  have hX : ((Wf s).fieldMap k (mField j)).1 U = ((Wf s).fieldMap k (mField j)).1 U' :=
    hS' U U' fun l hl => h l (hS'r l hl)
  simp only [msFlow, ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply,
    smul_eq_mul, hX]

/-- **The reading factors through the aperture**: `msFlow Wf k s j U = g(U|_aperture)` for one function `g`
of the configuration on the aperture. DERIVED: `1` the group unit off the aperture. -/
theorem msFlow_factors [NeZero N] (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (j : MIx) :
    ∃ g : (aperture Wf k s j → MassGap.SUN.SU N) → ℝ,
      ∀ U : Cfg N, msFlow Wf k s j U = g (fun l => U l.1) := by
  classical
  refine ⟨fun v => msFlow Wf k s j (fun l => if h : l ∈ aperture Wf k s j then v ⟨l, h⟩ else 1),
    fun U => ?_⟩
  exact msFlow_readsOn Wf k s j _ _ fun l hl => by simp [hl]

end Locality

/-! ## 2. The measured number of modes -/

section Measured

/-- **The Gram matrix of a screen under a state**: `ν(Fₓ F_y)`. DERIVED: no numeral. -/
def gram {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X) {ι : Type*}
    (F : ι → C(X, ℝ)) : Matrix ι ι ℝ :=
  fun x y => ν (F x * F y)

/-- DERIVED: no numeral. -/
theorem gram_isHermitian {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X)
    {ι : Type*} (F : ι → C(X, ℝ)) : (gram ν F).IsHermitian :=
  Matrix.IsHermitian.ext fun x y => by
    show star (ν (F y * F x)) = ν (F x * F y)
    rw [star_trivial, mul_comm]

/-- **The entropy-effective number of modes of a spectrum**: `exp(−∑ pᵢ log pᵢ)`, `p = w / ∑ w`
(the `2^H` of `entroptics.reads._fill_of` on `axis_spectrum`, in nats). DERIVED: no numeral. -/
def spDim {ι : Type*} [Fintype ι] (w : ι → ℝ) : ℝ :=
  Real.exp (∑ i, Real.negMulLog (w i / ∑ i', w i'))

/-- DERIVED: `0` the sign. -/
theorem spDim_pos {ι : Type*} [Fintype ι] (w : ι → ℝ) : 0 < spDim w := Real.exp_pos _

/-- **`n` equal modes read `n`**. DERIVED: no numeral. -/
theorem spDim_const {ι : Type*} [Fintype ι] [Nonempty ι] {c : ℝ} (hc : 0 < c) :
    spDim (fun _ : ι => c) = Fintype.card ι := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold spDim
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have e1 : c / ((Fintype.card ι : ℝ) * c) = (Fintype.card ι : ℝ)⁻¹ := by
    field_simp
  have e2 : (Fintype.card ι : ℝ) * Real.negMulLog (Fintype.card ι : ℝ)⁻¹ = Real.log (Fintype.card ι) := by
    rw [Real.negMulLog, Real.log_inv]
    field_simp
  rw [e1, e2, Real.exp_log hn]

/-- **One mode reads `1`**. DERIVED: `1` the one mode; `0` the empty modes. -/
theorem spDim_single {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) {c : ℝ} (hc : 0 < c) :
    spDim (Pi.single i₀ c : ι → ℝ) = 1 := by
  unfold spDim
  have hs : ∑ i', (Pi.single i₀ c : ι → ℝ) i' = c := by simp
  rw [hs]
  have h0 : ∑ i, Real.negMulLog ((Pi.single i₀ c : ι → ℝ) i / c) = 0 := Finset.sum_eq_zero fun i _ => by
    by_cases h : i = i₀
    · subst h
      rw [Pi.single_eq_same, div_self hc.ne', Real.negMulLog_one]
    · rw [Pi.single_eq_of_ne h, zero_div, Real.negMulLog_zero]
  rw [h0, Real.exp_zero]

/-- **The entropy-effective number of modes of a screen under a state**. DERIVED: no numeral. -/
def effDim {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (F : ι → C(X, ℝ)) : ℝ :=
  spDim (gram_isHermitian ν F).eigenvalues

/-- **The aperture's side in lattice steps**: `L = ⌈s / a_k⌉`. DERIVED: no numeral. -/
def apL (N : ℕ) (k : ℕ) (s : ℝ) : ℕ := ⌈s / dySpacing N k⌉₊

/-- A box site as a lattice vector. DERIVED: `4` the spacetime dimension. -/
def apSite {L : ℕ} (y : Fin 4 → Fin L) : ISite := fun μ => ((y μ : ℕ) : ℤ)

/-- **The screen**: the channel reading at every site of the aperture box `{0, …, L − 1}⁴`.
DERIVED: `4` the spacetime dimension. -/
def screen [NeZero N] (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (j : MIx) :
    (Fin 4 → Fin (apL N k s)) → C(Cfg N, ℝ) :=
  fun y => transObs (apSite y) (msFlow Wf k s j)

/-- **The measured number of modes of the observer's reading** at aperture `s` and step `k`.
DERIVED: no numeral. -/
def apDim [NeZero N] (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (j : MIx) : ℝ :=
  effDim (stateK (NeZero.ne N) k) (screen Wf k s j)

/-- DERIVED: `0` the sign. -/
theorem apDim_pos [NeZero N] (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (j : MIx) : 0 < apDim Wf k s j :=
  spDim_pos _

end Measured

/-! ## 3. The mechanism -/

/-- **The aperture reads a measured, bounded number of modes, each settling** (module docstring, §3).
DERIVED: `1` the limit of the ratio; `2` the even powers and the square; `4` the plaquette dimension; `8` the
dimension pair; `0` the signs and the point approached. -/
def ApertureModesAt [NeZero N] (b₀ : ℝ) (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop :=
  ∃ (u : ℝ) (γ : Ix0 → ℝ) (γP : ℝ), 0 < u ∧
    (∀ j : MIx, ∃ D : ℝ, ∀ s : ℝ, 0 < s → s ≤ b → ∀ᶠ k in atTop, apDim Wf k s j ≤ D)
    ∧ (∀ j : MIx, ∃ σ : ℝ, 0 < σ ∧ ∀ s : ℝ, 0 < s → s ≤ b → ∀ p : ℕ, ∀ᶠ k in atTop,
        stateK (NeZero.ne N) k (msFlow Wf k s j ^ (2 * p))
          ≤ ((2 * p).factorial : ℝ) ^ wickIx j * apDim Wf k s j ^ (2 * p)
            * (σ * runG b₀ u s ^ anom γ γP j / s ^ mDim j) ^ (2 * p))
    ∧ (∃ σP E DP : ℝ, 0 < σP ∧ ∀ᶠ k in atTop, ∀ q : MassGap.GibbsSpec.IPlaq,
        apDim Wf k b (Sum.inr q) ≤ DP
        ∧ |stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1| ≤ E * dySpacing N k ^ 4
        ∧ ∀ m : ℕ, stateK (NeZero.ne N) k (msFlow Wf k b (Sum.inr q) ^ (2 * m))
          ≤ ((2 * m).factorial : ℝ) * apDim Wf k b (Sum.inr q) ^ (2 * m) * σP ^ (2 * m))
    ∧ ∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) z) G
        ∧ Tendsto (fun r => r ^ 8 * G r / (trTree N * runG b₀ u r ^ 2)) (𝓝[>] 0) (𝓝 1)

set_option linter.dupNamespace false in
/-- **The aperture modes** at the one-loop coefficient of `SU(N)`. DERIVED: no numeral beyond `b0`'s. -/
def ApertureModes [NeZero N] (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop :=
  ApertureModesAt (MassGap.ClayStatement.b0 N) z b Wf

/-! ## 4. The derivations -/

/-- **The measured count replaced by its bound**: `ApertureModesAt` gives `ZoomFree.ApertureOneAt` at noise
`max(D, 1) σⱼ` and `max(DP, 1) σP`. DERIVED: `1` the floor of the bound; `2` the even powers; `0` the
signs. -/
theorem apertureOneAt_of_modes [NeZero N] {b₀ : ℝ} {z : Chan → ℕ → ℝ} {b : ℝ} {Wf : ℝ → ConfFlow N}
    (h : ApertureModesAt b₀ z b Wf) : ApertureOneAt b₀ z b Wf := by
  obtain ⟨u, γ, γP, hu, hdim, hset, ⟨σP, E, DP, hσP, hobs⟩, haf⟩ := h
  have hP1 : (0 : ℝ) < max DP 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨u, γ, γP, hu, fun j => ?_, ⟨max DP 1 * σP, E, mul_pos hP1 hσP, ?_⟩, haf⟩
  · obtain ⟨D, hD⟩ := hdim j
    obtain ⟨σ, hσ, hj⟩ := hset j
    have hD1 : (0 : ℝ) < max D 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    refine ⟨max D 1 * σ, mul_pos hD1 hσ, fun s hs hsb p => ?_⟩
    filter_upwards [hD s hs hsb, hj s hs hsb p] with k hkD hk
    have hle : apDim Wf k s j ^ (2 * p) ≤ max D 1 ^ (2 * p) :=
      pow_le_pow_left₀ (apDim_pos Wf k s j).le (hkD.trans (le_max_left _ _)) _
    have hX := Even.pow_nonneg (even_two_mul p) (σ * runG b₀ u s ^ anom γ γP j / s ^ mDim j)
    calc stateK (NeZero.ne N) k (msFlow Wf k s j ^ (2 * p))
        ≤ ((2 * p).factorial : ℝ) ^ wickIx j * apDim Wf k s j ^ (2 * p)
            * (σ * runG b₀ u s ^ anom γ γP j / s ^ mDim j) ^ (2 * p) := hk
      _ ≤ ((2 * p).factorial : ℝ) ^ wickIx j * max D 1 ^ (2 * p)
            * (σ * runG b₀ u s ^ anom γ γP j / s ^ mDim j) ^ (2 * p) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by positivity)) hX
      _ = ((2 * p).factorial : ℝ) ^ wickIx j
            * (max D 1 * σ * runG b₀ u s ^ anom γ γP j / s ^ mDim j) ^ (2 * p) := by ring
  · filter_upwards [hobs] with k hk q
    obtain ⟨hkD, hmean, hmom⟩ := hk q
    refine ⟨hmean, fun m => ?_⟩
    have hle : apDim Wf k b (Sum.inr q) ^ (2 * m) ≤ max DP 1 ^ (2 * m) :=
      pow_le_pow_left₀ (apDim_pos Wf k b _).le (hkD.trans (le_max_left _ _)) _
    calc stateK (NeZero.ne N) k (msFlow Wf k b (Sum.inr q) ^ (2 * m))
        ≤ ((2 * m).factorial : ℝ) * apDim Wf k b (Sum.inr q) ^ (2 * m) * σP ^ (2 * m) := hmom m
      _ ≤ ((2 * m).factorial : ℝ) * max DP 1 ^ (2 * m) * σP ^ (2 * m) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by positivity))
            (pow_nonneg hσP.le _)
      _ = ((2 * m).factorial : ℝ) * (max DP 1 * σP) ^ (2 * m) := by ring

/-- `ApertureModesAt` gives `ZoomFree.ApertureSettlesAt` (`apertureSettlesAt_iff_one`). DERIVED: no
numeral. -/
theorem apertureSettlesAt_of_modes [NeZero N] {b₀ : ℝ} {z : Chan → ℕ → ℝ} {b : ℝ} {Wf : ℝ → ConfFlow N}
    (h : ApertureModesAt b₀ z b Wf) : ApertureSettlesAt b₀ z b Wf :=
  apertureSettlesAt_iff_one.2 (apertureOneAt_of_modes h)

/-- **The coincident-point core from the measured aperture modes**: `ApertureModes z b Wf`, `b > 0` and
`Wf b = W` give `SubstrateCoreCL W z b Wf`. DERIVED: `2` the least colour count; `0` the sign. -/
theorem substrateCoreCL_of_apertureModes (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ}
    {b : ℝ} {Wf : ℝ → ConfFlow N} (hb : 0 < b) (htop : Wf b = W) (h : ApertureModes z b Wf) :
    SubstrateCoreCL W z b Wf :=
  substrateCoreCL_of_aperture hN2 hb htop (apertureSettlesAt_of_modes h)

/-! ## 5. The tests -/

/-- **The per-mode noise settles at `b₀ > 0`**: `ḡ²(s)^κ → 0` as `s → 0⁺` for `κ > 0`. DERIVED: `0` the
point approached, the limit and the sign. -/
theorem tendsto_runG_rpow_zero {b₀ u κ : ℝ} (hb : 0 < b₀) (hu : 0 < u) (hκ : 0 < κ) :
    Tendsto (fun s => runG b₀ u s ^ κ) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_runG_zero hb hu).rpow_const (Or.inr hκ.le)
  rwa [Real.zero_rpow hκ.ne'] at h

/-- **At `b₀ = 0` the per-mode noise does not settle**: `ḡ²(s)^κ = u^κ` at every `s`. DERIVED: `0` the
coefficient. -/
theorem runG_zero_rpow (u κ s : ℝ) : runG 0 u s ^ κ = u ^ κ := by
  simp [runG]

end MassGap.ApertureModes

end

/-! ### The copy over a coupling family -/

namespace MassGap.ApertureModes

set_option Elab.async false in
set_option maxHeartbeats 0 in
#along_generalize_more MassGap.ContinuumSchwinger.dyBeta from
  MassGap.ApertureModes.substrateCoreCL_of_apertureModes

-- No copy mentions the source (every copy in `MassGap.CouplingGen.Along`, the new ones included).
run_cmd do
  let env ← Lean.getEnv
  let src := ``MassGap.ContinuumSchwinger.dyBeta
  let pre := `MassGap.CouplingGen.Along
  for (c, ci) in env.constants.map₂.toList do
    if pre.isPrefixOf c then
      let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
      if used.contains src then
        throwError "copy {c} still mentions {src}"

end MassGap.ApertureModes

/-! ## 6. The root -/

noncomputable section

namespace MassGap.ApertureModes

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.ClayTreeG MassGap.ClayStatementG MassGap.FlowG Filter
open scoped Topology
open MassGap.FlowAlong (cpl)
open MassGap.CouplingTower (StrongEnd CouplingTower UVConverges)
open MassGap.CompositeLink (Φ0)
open MassGap.CompositesRen (OffMix)
open MassGap.ScaleLightCone (CoreInputsAlongWSL ZoomSettlesUV clayStatementOf_of_zoomSettles)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

variable (N) in
/-- **The flow-side bundle along `βs` with the measured aperture modes**: `ZoomFree.CoreInputsAlongWAP`
with the copy of `ApertureModes z b Wf` in place of the copy of `ApertureSettles z b Wf`, every other field
unchanged. DERIVED: `0` the signs. -/
def CoreInputsAlongWAM (βs : ℕ → ℝ) : Prop :=
  ∃ (W : ConfFlow N) (r : ℝ) (_ : (Φ0 W).PhysRange r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)),
    0 < b ∧ Wf b = W
      ∧ CouplingGen.Along.ApertureModes.ApertureModes (cpl βs) (ZCanon.zFix N zri zwe) b Wf
      ∧ CouplingGen.Along.StrongExpand.ExpandStrong (cpl βs) Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CouplingGen.Along.ScaleLightCone.ZoomSettles (cpl βs) Wf cf
      ∧ CouplingGen.Along.FlowCovN.FlowCovLim (cpl βs) Wf cf
      ∧ CouplingGen.Along.WardFromLattice.FlowWard (cpl βs) Wf cf
      ∧ CouplingGen.Along.NondegFromProxy.ProxyNondeg (cpl βs) Wf cf
      ∧ CouplingGen.Along.ProxyGenLimN.ProxyGenLimGerm (cpl βs) W b Wf cf r
      ∧ ∃ ℓ : ℝ, 0 < ℓ
          ∧ CouplingGen.Along.NonGaussFromScale.ThreePointAtScale (cpl βs) (NeZero.ne N) ℓ

/-- **The measured-modes bundle gives the separated-zoom bundle** (the copy of
`substrateCoreCL_of_apertureModes` at `cpl βs`). DERIVED: `2` the least colour count. -/
theorem coreWSL_of_coreWAM {βs : ℕ → ℝ} (h : CoreInputsAlongWAM N βs) : CoreInputsAlongWSL N βs := by
  obtain ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, hb, htop, hZ, hE, F⟩ := h
  exact ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf,
    CouplingGen.Along.ApertureModes.substrateCoreCL_of_apertureModes (cpl βs) (Fact.out : 2 ≤ N) hb htop hZ,
    hE, F⟩

/-- **The root at `SU(N)` from the strong end, the separated zoom and the measured aperture modes**:
`StrongEnd N`, the settling window reading and `CoreInputsAlongWAM` along the towers near `0⁺` give
`ClayStatementOf (SU N)` (`ScaleLightCone.clayStatementOf_of_zoomSettles`, `coreWSL_of_coreWAM`).
DERIVED: `0` the limit `0⁺`. -/
theorem clayStatementOf_of_apertureModes (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ZoomSettlesUV N βs)
    (hF : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      CoreInputsAlongWAM N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  clayStatementOf_of_zoomSettles hS hUV (hF.mono fun _ h βs hT => coreWSL_of_coreWAM (h βs hT))

end MassGap.ApertureModes

end

#print axioms MassGap.ApertureModes.msFlow_readsOn
#print axioms MassGap.ApertureModes.msFlow_factors
#print axioms MassGap.ApertureModes.gram_isHermitian
#print axioms MassGap.ApertureModes.spDim_pos
#print axioms MassGap.ApertureModes.spDim_const
#print axioms MassGap.ApertureModes.spDim_single
#print axioms MassGap.ApertureModes.apDim_pos
#print axioms MassGap.ApertureModes.apertureOneAt_of_modes
#print axioms MassGap.ApertureModes.apertureSettlesAt_of_modes
#print axioms MassGap.ApertureModes.substrateCoreCL_of_apertureModes
#print axioms MassGap.CouplingGen.Along.ApertureModes.substrateCoreCL_of_apertureModes
#print axioms MassGap.ApertureModes.tendsto_runG_rpow_zero
#print axioms MassGap.ApertureModes.runG_zero_rpow
#print axioms MassGap.ApertureModes.coreWSL_of_coreWAM
#print axioms MassGap.ApertureModes.clayStatementOf_of_apertureModes
