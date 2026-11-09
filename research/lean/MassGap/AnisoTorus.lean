import Mathlib
import MassGap.LayerSplit
import MassGap.BetaAnalytic

/-!
# MassGap.AnisoTorus — the anisotropic Wilson torus and a Vitali transport in the mixed coupling

The bridge is `CouplingTower.StrongEnd N`: frequently as `β → ∞`, `windowCoupling N β w → 0` along the windows.
This module builds the anisotropic Wilson torus on the tree's configuration space, identifies its isotropic end
with the window coupling, and transports a small-`β_⊥` anchor to `β_⊥ = β` by Vitali's theorem in the mixed
coupling. No rate is used. Declarations are in `MassGap.AnisoTorus`.

## 1. The anisotropic torus (proved definitions and isotropic end)

Configuration space and measure are those of `TorusDoubling.sysT (SU N) 4 n wilsonDensity`, the system of
`TorusDoubling.ZT` and of `RectWilson.ZR` at equal extents: one `SU(N)` element per link, `probHaar` on every
link. The plaquettes are the tree's ordered pairs of directions with a site. CHOSEN: the in-plane orientations
are the pairs inside `{0, 1}` or inside `{2, 3}` (`inPlane`); any complementary pair of planes serves by the
permutation symmetry of the directions. The diagonal pairs fall in-plane and read `φ(1) = 0`, for `N ≠ 0`.

* `Sin`, `Smix`: the plaquette sum restricted to the in-plane and to the mixed orientations.
* `sin_add_smix`: `S_in + S_mix` is the tree's action, by splitting the sum over orientations.
* `ZA N β β_⊥ n = ∫ e^{−(β S_in + β_⊥ S_mix)}`, `logZA`, and the anisotropic window defect
  `DA N β β_⊥ w = 16 log ZA(2^w) − log ZA(2^{w+1})`.
* `ZA_iso`: `ZA N β β n = ZR (fun _ => n) N β`. `DA_iso`: `DA N β β w = windowCoupling N β w`.

## 2. The decoupled end (named input, proved consequences)

At `β_⊥ = 0` a link of direction `0` or `1` enters only `(0,1)` plaquettes and one of direction `2` or `3` only
`(2,3)` plaquettes; the `(0,1)` plaquettes at fixed `(x₂, x₃)` form a 2D torus of side `n`, so by Fubini over the
product Haar measure `log ZA(β, 0, n) = 2 n² log Z₂(β, n)`, `Z₂ = ZT (SU N) 2 wilsonDensity`. This module
states the factorization as the named input `DecoupledFactor N β`; `DecoupledSplit.decoupledFactor` proves it for every
`N`, `β`. `DA_decoupled`: under it, `DA N β 0 w = LayerSplit.layerDefect N β w`; `decoupled_vanishes`: with
`LayerSplit.TwoDCharacter N β`, `DA N β 0 · → 0`. The vanishing itself is proved without that input in
`TwoDVanish.decoupled_vanishes`.

## 3. The Vitali transport in `β_⊥` (named inputs, proved bridge)

`AnisoAnalytic N β`: a preconnected open `Ω ⊆ ℂ` containing `(0, ε)` and the point `β`, and a holomorphic
extension of `β_⊥ ↦ DA N β β_⊥ w` on `Ω`, locally bounded uniformly in `w`. `WeakMixAnchor N β`: on some
`(0, b)`, `DA N β β_⊥ · → 0`; proved at every `β ≥ 0` in `TwoDVanish.weakMixAnchor`, and from
`LayerSplit.TwoDCharacter N β` in `MixAnchor.weakMixAnchor_of_twoD`. `tendsto_of_anchor` (Vitali through `BetaAnalytic.vitali_tendsto_zero`) carries the anchor to
every real point of `Ω`, and `strongEnd_of_aniso`: frequently in `β`, `AnisoAnalytic N β ∧ WeakMixAnchor N β`
gives `StrongEnd N`, through `DA_iso`. No rate and no window-independent constant enter.

## 4. Why an anchor interval and not the decoupled point

The decoupled end `β_⊥ = 0` is a single point. Vitali needs the convergence on a set accumulating at a point of
`Ω`; a single point does not accumulate, so `decoupled_vanishes` alone cannot feed the transport. Vanishing at
`β_⊥ = 0` does give the anchor (`MixAnchor.weakMixAnchor_of_decoupled`): continuity at one fixed window seeds
the doubling basin on `[0, b)`, and the basin squaring `MixAnchor.DA_succ_le` holds at every window, which
supplies the uniformity in `w`.

## 5. U(1) (argued)

The decoupled end and a small-`β_⊥` expansion around 2D planes do not use non-abelian structure, so the anchor is
expected for `U(1)` too. At large `β` and `β_⊥ = β` the 4D `U(1)` theory is in its Coulomb phase (Guth;
Fröhlich–Spencer) and its window coupling stalls, so the conclusion of `strongEnd_of_aniso` fails there; for
`U(1)`, if the anchor holds, `AnisoAnalytic` fails there (a phase transition in `β_⊥` on `(0, β)`); this is
argued, not proved. The non-abelian content sits in `AnisoAnalytic`.
-/

namespace MassGap.AnisoTorus

open MeasureTheory Filter Topology Set MassGap MassGap.LatticeGauge
open MassGap.CouplingTower (windowCoupling StrongEnd)

/-! ## 1. The anisotropic torus -/

/-- The tree's 4D Wilson system on the side-`n` torus (`TorusDoubling.sysT` at `SU(N)`, `d = 4`). DERIVED: `4`
the dimension. -/
noncomputable abbrev sys4 (N n : ℕ) : System (SUN.SU N) :=
  TorusDoubling.sysT (SUN.SU N) 4 n WilsonAction.wilsonDensity

/-- **The in-plane orientations**: both directions in `{0, 1}` or both in `{2, 3}`. CHOSEN: the complementary
pair `(0,1)`, `(2,3)` (any complementary pair serves by symmetry). DERIVED: `2` the size of each plane's direction
block. -/
def inPlane (o : Fin 4 × Fin 4) : Bool := o.1.val / 2 == o.2.val / 2

/-- **The in-plane action** `S_in`: the plaquette density summed over the in-plane orientations. DERIVED: `0`
the excluded terms; `4` the dimension. -/
noncomputable def Sin (N n : ℕ) (U : (sys4 N n).Config) : ℝ :=
  ∑ q : TorusDoubling.TPlaq 4 n, if inPlane q.1 then (sys4 N n).φ ((sys4 N n).hol q U) else 0

/-- **The mixed action** `S_mix`: the plaquette density summed over the eight mixed ordered orientations (four
unordered pairs). DERIVED: `0` the excluded terms. -/
noncomputable def Smix (N n : ℕ) (U : (sys4 N n).Config) : ℝ :=
  ∑ q : TorusDoubling.TPlaq 4 n, if inPlane q.1 then 0 else (sys4 N n).φ ((sys4 N n).hol q U)

/-- **The split of the action over orientations**: `S_in + S_mix = S`. DERIVED: `0` the excluded terms. -/
theorem sin_add_smix (N n : ℕ) (U : (sys4 N n).Config) :
    Sin N n U + Smix N n U = (sys4 N n).action U := by
  unfold Sin Smix System.action
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : inPlane q.1 = true <;> simp [h]

/-- **The anisotropic partition function** `ZA = ∫ e^{−(β S_in + β_⊥ S_mix)}` against the tree's product Haar
measure. No numeral. -/
noncomputable def ZA (N : ℕ) (β βp : ℝ) (n : ℕ) : ℝ :=
  ∫ U, Real.exp (-(β * Sin N n U + βp * Smix N n U)) ∂((sys4 N n).vol (CompactGauge.probHaar (SUN.SU N)))

/-- `log ZA`. No numeral. -/
noncomputable def logZA (N : ℕ) (β βp : ℝ) (n : ℕ) : ℝ := Real.log (ZA N β βp n)

/-- **The anisotropic window defect** `16 log ZA(2^w) − log ZA(2^{w+1})`. DERIVED: `16 = 2⁴` the copies; `2` the
doubling; `1` the next window. -/
noncomputable def DA (N : ℕ) (β βp : ℝ) (w : ℕ) : ℝ :=
  16 * logZA N β βp (2 ^ w) - logZA N β βp (2 ^ (w + 1))

/-- **The isotropic end, partition function**: `ZA N β β n = ZR (fun _ => n) N β`. No numeral. -/
theorem ZA_iso (N : ℕ) (β : ℝ) (n : ℕ) : ZA N β β n = RectWilson.ZR (fun _ => n) N β := by
  rw [← TorusDoubling.ZT_four_eq]
  unfold ZA TorusDoubling.ZT System.partition System.boltz
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  dsimp only
  rw [← mul_add, sin_add_smix, neg_mul]

/-- **The isotropic end**: `DA N β β w = windowCoupling N β w`. DERIVED: `2` the doubling. -/
theorem DA_iso (N : ℕ) (β : ℝ) (w : ℕ) : DA N β β w = windowCoupling N β w := by
  unfold DA logZA windowCoupling ZoomSelfScale.defectW
  rw [ZA_iso, ZA_iso, show 2 ^ (w + 1) = 2 * 2 ^ w from pow_succ' 2 w]

/-! ## 2. The decoupled end -/

/-- **`DecoupledFactor N β`, a named input, not proved here**: the Fubini factorization at `β_⊥ = 0`,
`log ZA(β, 0, n) = 2 n² log Z₂(β, n)` with `Z₂ = TorusDoubling.ZT (SU N) 2 wilsonDensity` (argued in the module
docstring; the measurable splitting of the link product is not built). DERIVED: `0` the decoupled end; `2` the
complementary planes; `n²` the transverse sites of each; `1` the least side. -/
def DecoupledFactor (N : ℕ) (β : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → logZA N β 0 n = 2 * (n : ℝ) ^ 2 * LayerSplit.logZ2 N β n

/-- **The decoupled end is the layered defect**: under `DecoupledFactor N β`,
`DA N β 0 w = LayerSplit.layerDefect N β w`. DERIVED: `2` the doubling; `0` the decoupled end. -/
theorem DA_decoupled {N : ℕ} {β : ℝ} (h : DecoupledFactor N β) (w : ℕ) :
    DA N β 0 w = LayerSplit.layerDefect N β w := by
  have h1 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 * 2 ^ w := by omega
  unfold DA LayerSplit.layerDefect LayerSplit.logZLayer
  rw [show 2 ^ (w + 1) = 2 * 2 ^ w from pow_succ' 2 w, h _ h1, h _ h2]

/-- **The decoupled end vanishes**: `DecoupledFactor N β` and the cited `TwoDCharacter N β` give
`DA N β 0 · → 0`. DERIVED: `0` the decoupled end and the limit. -/
theorem decoupled_vanishes {N : ℕ} {β : ℝ} (h : DecoupledFactor N β) (hC : LayerSplit.TwoDCharacter N β) :
    Tendsto (fun w => DA N β 0 w) atTop (𝓝 0) :=
  (LayerSplit.layer_vanishes hC).congr fun w => (DA_decoupled h w).symm

/-! ## 3. The Vitali transport in `β_⊥` -/

/-- **`AnisoAnalytic N β`, a named input, not proved**: a preconnected open `Ω ⊆ ℂ` containing `(0, ε)`, `ε > 0`
existential, and the point `β`, with a holomorphic extension of `β_⊥ ↦ DA N β β_⊥ w` on `Ω`, locally bounded
uniformly in `w`. Expected to fail for `U(1)` (module docstring, §5). DERIVED: `0` the lower end. -/
def AnisoAnalytic (N : ℕ) (β : ℝ) : Prop :=
  ∃ (Ω : Set ℂ) (F : ℕ → ℂ → ℂ), IsOpen Ω ∧ IsPreconnected Ω ∧
    (∃ ε > 0, ∀ x : ℝ, 0 < x → x < ε → (x : ℂ) ∈ Ω) ∧ (β : ℂ) ∈ Ω ∧
    BetaAnalytic.HoloExtensionOf (fun βp w => DA N β βp w) Ω F ∧ BetaAnalytic.LocBounded Ω F

/-- **`WeakMixAnchor N β`**: on some interval `(0, b)` of mixed couplings, `DA N β β_⊥ · → 0`. Proved from
`TwoDCharacter N β` at `β ≥ 0` in `MixAnchor.weakMixAnchor_of_twoD`. DERIVED: `0` the decoupled end
and the limit. -/
def WeakMixAnchor (N : ℕ) (β : ℝ) : Prop :=
  ∃ b > 0, ∀ βp : ℝ, 0 < βp → βp < b → Tendsto (fun w => DA N β βp w) atTop (𝓝 0)

/-- **Vitali transport of an interval anchor**: a reading with a locally bounded holomorphic extension on a
preconnected open `Ω ⊇ (0, ε)`, vanishing on `(0, b)`, vanishes at every real `x ≥ 0` in `Ω`. DERIVED: `0` the
lower end and the limit; `2` the midpoint of the anchor interval (any interior point serves). -/
theorem tendsto_of_anchor {D : ℝ → ℕ → ℝ} {Ω : Set ℂ} {F : ℕ → ℂ → ℂ} (hΩo : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hεΩ : ∃ ε > 0, ∀ x : ℝ, 0 < x → x < ε → (x : ℂ) ∈ Ω)
    (hE : BetaAnalytic.HoloExtensionOf D Ω F) (hbd : BetaAnalytic.LocBounded Ω F)
    (hanc : ∃ b > 0, ∀ t : ℝ, 0 < t → t < b → Tendsto (D t) atTop (𝓝 0))
    {x : ℝ} (hx0 : 0 ≤ x) (hx : (x : ℂ) ∈ Ω) : Tendsto (D x) atTop (𝓝 0) := by
  obtain ⟨b, hb, hanc⟩ := hanc
  obtain ⟨ε, hε, hεΩ⟩ := hεΩ
  set e := min ε b with he_def
  have he : 0 < e := lt_min hε hb
  let A : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Ioo 0 e
  have hAΩ : A ⊆ Ω := by
    rintro _ ⟨t, ⟨h0, h1⟩, rfl⟩
    exact hεΩ t h0 (lt_of_lt_of_le h1 (min_le_left _ _))
  have hA : ∀ z ∈ A, Tendsto (fun w => F w z) atTop (𝓝 0) := by
    rintro _ ⟨t, ⟨h0, h1⟩, rfl⟩
    have ht := hanc t h0 (lt_of_lt_of_le h1 (min_le_right _ _))
    have hagree : (fun w => F w (t : ℂ)) = fun w => ((D t w : ℝ) : ℂ) :=
      funext fun w => hE.agree w t h0.le (hAΩ ⟨t, ⟨h0, h1⟩, rfl⟩)
    rw [hagree]
    have h' := (Complex.continuous_ofReal.tendsto 0).comp ht
    rw [Complex.ofReal_zero] at h'
    exact h'
  have hmid : e / 2 ∈ Ioo 0 e := ⟨half_pos he, half_lt_self he⟩
  have hall := BetaAnalytic.vitali_tendsto_zero hΩo hΩc hE.holo hbd hAΩ hA (hAΩ ⟨e / 2, hmid, rfl⟩)
    (BetaAnalytic.frequently_ofReal_Ioo hmid.1 hmid.2)
  have h := hall _ hx
  have hagree : (fun w => F w (x : ℂ)) = fun w => ((D x w : ℝ) : ℂ) :=
    funext fun w => hE.agree w x hx0 hx
  rw [hagree] at h
  have h' := (Complex.continuous_re.tendsto 0).comp h
  simp only [Function.comp_def, Complex.ofReal_re, Complex.zero_re] at h'
  exact h'

/-- **The anisotropic transport gives the strong end**: frequently as `β → ∞`, `AnisoAnalytic N β` and
`WeakMixAnchor N β` give `StrongEnd N`, through Vitali in `β_⊥` and `DA_iso`. No rate. DERIVED: `0` the lower
coupling. -/
theorem strongEnd_of_aniso {N : ℕ}
    (h : ∃ᶠ β in atTop, AnisoAnalytic N β ∧ WeakMixAnchor N β) : StrongEnd N := by
  refine (h.and_eventually (eventually_ge_atTop (0 : ℝ))).mono ?_
  rintro β ⟨⟨⟨Ω, F, hΩo, hΩc, hε, hβΩ, hE, hbd⟩, hanc⟩, hβ⟩
  have ht := tendsto_of_anchor (D := fun βp w => DA N β βp w) hΩo hΩc hε hE hbd hanc hβ hβΩ
  exact ht.congr fun w => DA_iso N β w

end MassGap.AnisoTorus

#print axioms MassGap.AnisoTorus.sin_add_smix
#print axioms MassGap.AnisoTorus.ZA_iso
#print axioms MassGap.AnisoTorus.DA_iso
#print axioms MassGap.AnisoTorus.DA_decoupled
#print axioms MassGap.AnisoTorus.decoupled_vanishes
#print axioms MassGap.AnisoTorus.tendsto_of_anchor
#print axioms MassGap.AnisoTorus.strongEnd_of_aniso
