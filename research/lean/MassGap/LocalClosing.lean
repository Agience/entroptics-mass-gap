import Mathlib
import MassGap.LightConePassage
import MassGap.PeriodicStateDLR

noncomputable section

/-!
# MassGap.LocalClosing — the torus against infinite volume, read through a box

The torus and the infinite volume are compared on a local reading by conditioning both on a box `Λ`
around the reading. Both are DLR states of the same Wilson specification on `Λ`
(`PeriodicStateDLR.torusState_dlr`, `periodicState_dlr`), so both read `f` as they read its box
kernel `wspec β Λ f`, and the two readings differ by at most the spread of that kernel over boundary
conditions. Nothing in the bound reads the torus extent: once `Λ` fits, the capacity outside it never
enters.

## 1. A DLR state reads a local observable through its box kernel (proved)

For any compact `X`, any `DLRLimit.State X`, any kernel `K`:

* `le_of_forall_le`, `ge_of_forall_ge`: a pointwise bound passes to the state;
* `abs_sub_le_of_forall` and `abs_sub_le_of_osc`: a state within `δ` of `r` pointwise, and two states
  apart by at most the oscillation `δ`;
* `abs_le_of_kernel`: `ν (K f) = ν f` and `|K f ω − r| ≤ δ` at every `ω` give `|ν f − r| ≤ δ`;
* `local_closing`: two states, both DLR for `K` at `f`, differ on `f` by at most the oscillation of
  `K f`.

## 2. The Wilson torus against the infinite volume (proved, capacity-free)

`BoxFits M Λ S` is the injectivity of the reduction modulo `M + 1` that `torusState_dlr` uses.

* `torus_local_closing`: for `f` local on `S`, `BoxFits M Λ S` and the box kernel spread `≤ δ`,
  `|torusState hN M β f − periodicState hN β f| ≤ δ`. The bound does not contain `M`.
* `boxFits_eventually`, `torus_local_closing_uniform`: one bound for every extent past a threshold.

## 3. The reference reading (proved)

* `refObs ν O t ℓ k`: the reflected and the plain cube field, each centred by its one-point value in
  `ν`, multiplied; `refReadingS_eq`: `refReadingS σ O t ℓ k = σ k (refObs (σ k) O t ℓ k)`.
* `pixel_split`: the infinite-volume reading against the reading in `σ` splits into the two states on
  one composite (the infinite-volume one), plus the change of centring inside `σ`.
* `BoxPixel hN c O t ℓ π₁`: eventually in `k` a box `Λ` that fits in the torus of `stateTD hN c k`,
  holds the support of the composite, and on which the box kernel of the composite spreads by at most
  `π₁ · √(refMomentS)` over boundary conditions. `CentringPixel hN c O t ℓ π₂`: the change of centring
  inside the torus is at most `π₂ · √(refMomentS)`.
* `pixelPassage_of_box`: the two give `PixelPassage hN (stateTD hN c) O t ℓ (π₁ + π₂)`;
  `clay_canonical_box` is `ExistenceReduce.clay_canonical` with `hpos` read through them and
  `ReadingFloor`.

## 4. The centring is second order (proved)

* `wsum a f`, the cell weight `∑ₓ a⁴ f(a x)`; `smear_sub_eq`: `smear a (O − r) f = smear a O f − r ·
  wsum a f`; `state_smear`: a translation-invariant state reads `smear a F f` as `wsum a f · ν F`.
* `refObs_eq`: the composite is the product of the two centred cube fields.
* `centring_identity`: in any state, changing the two subtracted constants changes the reading by two
  first-order terms and the product of the changes.
* `centring_eq`: on `stateTD hN c k`, translation invariant by `torusState_shift`, the first-order
  terms vanish, and the centring term is `(W₀ Δ₀)(W₁ Δ₁)`: cube weights times the one-point differences
  (infinite volume minus torus) of the reflected and the plain single-site field.
* `OnePointPixel hN c O t ℓ π`: eventually, boxes that fit in the torus around the two single-site
  fields with kernel spreads `δ₀`, `δ₁` and `|W₀| δ₀ · |W₁| δ₁ ≤ π · √(refMomentS)`.
  `centringPixel_of_onePoint`: it gives `CentringPixel`. `pixelPassage_of_boundary`: `BoxPixel` and
  `OnePointPixel` give `PixelPassage`; `clay_canonical_boundary` is the pinned path with `hpos` so read.

## 5. Clustering does not close the comparison (proved, witness)

`dirac x`, the point state at `x`. Under the frozen kernel (`K f = f`: the box carries no freedom,
the degenerate case of a specification) every point state is DLR (`dirac_isDLR_frozen`) and has no
connected correlation at all (`dirac_mul`). `clustering_does_not_close`: two such states on `Bool`
differ by `1` on an observable bounded by `1`. Exact clustering inside each DLR state, the strongest
form of a gap, says nothing about the difference of two DLR states; `local_closing` is sharp there
(`dirac_closing_eq`): the difference is the spread of the box kernel.

## What stays open

`BoxPixel` is not proved. It is decay of boundary influence: the box reading of a local observable
forgets the boundary condition at distance `d` from its support. That is a mixing property of the
specification (weak mixing in the sense of Dobrushin–Shlosman), quantified over every boundary
condition. The gap (`LightConePassage.relDecay_of_WDelta2_dir`) is a property of one state, the
infinite-volume one, and section 4 shows that a property of that kind does not bound the spread over
boundary conditions. On `stateTD hN c` the box can have physical side up to `2^c · aRun N 1`, so the
distance from the composite's support to `∂Λ` grows with `c` at fixed `k`; under weak mixing at the
physical rate `m` the spread is `≈ exp(−m · 2^{c−1} · aRun N 1)` times the second moment (argued).
`OnePointPixel` is not proved either; it is the same property at the single-site field, and it enters
squared (`centring_eq`). The remainder of (1b) on this route is boundary influence and nothing else:
`BoxPixel ∧ OnePointPixel` (`pixelPassage_of_boundary`).
-/

namespace MassGap.LocalClosing

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.TorusCapstone Filter

/-! ## 1. A DLR state reads a local observable through its box kernel -/

section Generic

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- A pointwise upper bound passes to the state. -/
theorem le_of_forall_le (ν : MassGap.DLRLimit.State X) {g : C(X, ℝ)} {c : ℝ}
    (h : ∀ x, g x ≤ c) : ν g ≤ c := by
  have hm := ν.mono (f := g) (g := c • (1 : C(X, ℝ))) (fun x => by
    simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
    exact h x)
  rwa [ν.map_smul, ν.map_one, mul_one] at hm

/-- A pointwise lower bound passes to the state. -/
theorem ge_of_forall_ge (ν : MassGap.DLRLimit.State X) {g : C(X, ℝ)} {c : ℝ}
    (h : ∀ x, c ≤ g x) : c ≤ ν g := by
  have hm := ν.mono (f := c • (1 : C(X, ℝ))) (g := g) (fun x => by
    simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
    exact h x)
  rwa [ν.map_smul, ν.map_one, mul_one] at hm

/-- An observable within `δ` of `r` at every point has its state value within `δ` of `r`. -/
theorem abs_sub_le_of_forall (ν : MassGap.DLRLimit.State X) {g : C(X, ℝ)} {r δ : ℝ}
    (h : ∀ x, |g x - r| ≤ δ) : |ν g - r| ≤ δ := by
  have h1 : ν g ≤ r + δ := le_of_forall_le ν (fun x => by linarith [(abs_le.mp (h x)).2])
  have h2 : r - δ ≤ ν g := ge_of_forall_ge ν (fun x => by linarith [(abs_le.mp (h x)).1])
  rw [abs_le]
  constructor <;> linarith

/-- **Two states differ on an observable by at most its oscillation.** -/
theorem abs_sub_le_of_osc (ν₁ ν₂ : MassGap.DLRLimit.State X) {g : C(X, ℝ)} {δ : ℝ}
    (h : ∀ x y, |g x - g y| ≤ δ) : |ν₁ g - ν₂ g| ≤ δ := by
  have hup : ∀ (ν : MassGap.DLRLimit.State X) (y : X), ν g ≤ g y + δ := fun ν y =>
    le_of_forall_le ν (fun x => by linarith [(abs_le.mp (h x y)).2])
  have h12 : ν₁ g - δ ≤ ν₂ g := ge_of_forall_ge ν₂ (fun y => by linarith [hup ν₁ y])
  have h21 : ν₂ g - δ ≤ ν₁ g := ge_of_forall_ge ν₁ (fun y => by linarith [hup ν₂ y])
  rw [abs_le]
  constructor <;> linarith

/-- **A DLR state against a value, through the kernel**: `ν (K f) = ν f` and `|K f ω − r| ≤ δ` at
every boundary condition `ω` give `|ν f − r| ≤ δ`. -/
theorem abs_le_of_kernel (K : C(X, ℝ) → C(X, ℝ)) (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ))
    (hK : ν (K f) = ν f) {r δ : ℝ} (h : ∀ x, |K f x - r| ≤ δ) : |ν f - r| ≤ δ := by
  rw [← hK]
  exact abs_sub_le_of_forall ν h

/-- **The local closing**: two states, both DLR for the kernel `K` at `f`, differ on `f` by at most
the oscillation of the box reading `K f` over boundary conditions. -/
theorem local_closing (K : C(X, ℝ) → C(X, ℝ)) (ν₁ ν₂ : MassGap.DLRLimit.State X) (f : C(X, ℝ))
    (h₁ : ν₁ (K f) = ν₁ f) (h₂ : ν₂ (K f) = ν₂ f) {δ : ℝ}
    (hosc : ∀ x y, |K f x - K f y| ≤ δ) : |ν₁ f - ν₂ f| ≤ δ := by
  rw [← h₁, ← h₂]
  exact abs_sub_le_of_osc ν₁ ν₂ hosc

end Generic

/-! ## 2. The Wilson torus against the infinite volume -/

section Wilson

variable {N : ℕ}

/-- The box `Λ`, its boundary links and the support `S` reduce injectively modulo `M + 1`, and so do
the boundary plaquettes of `Λ`: the hypotheses of `PeriodicStateDLR.torusState_dlr`. -/
def BoxFits (M : ℕ) (Λ S : Finset MassGap.GibbsSpec.ILink) : Prop :=
  Set.InjOn (MassGap.InfiniteLattice.linkMod M)
      ((S ∪ Λ ∪ MassGap.WilsonDLR.bdLinks Λ : Finset MassGap.GibbsSpec.ILink) :
        Set MassGap.GibbsSpec.ILink)
    ∧ Set.InjOn (MassGap.InfiniteLattice.plaqMod M)
      (MassGap.GibbsSpec.boundaryPlaqs Λ : Set MassGap.GibbsSpec.IPlaq)

/-- **The torus against the infinite volume on a local observable.** For `f` local on `S` and a box
`Λ` that fits in the torus of extent `M + 1`, the torus and the infinite-volume periodic state at the
same coupling differ on `f` by at most the spread of the box kernel `wspec β Λ f` over boundary
conditions. The bound does not contain `M`. -/
theorem torus_local_closing (hN : N ≠ 0) (M : ℕ) (β : ℝ) {Λ S : Finset MassGap.GibbsSpec.ILink}
    {f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)} (hf : MassGap.DLRLimit.IsLocalOnC S f)
    (hfit : BoxFits M Λ S) {δ : ℝ}
    (hosc : ∀ ω ω', |MassGap.PeriodicStateDLR.wspec hN β Λ f ω
      - MassGap.PeriodicStateDLR.wspec hN β Λ f ω'| ≤ δ) :
    |MassGap.PeriodicState.torusState hN M β f - MassGap.PeriodicState.periodicState hN β f| ≤ δ :=
  local_closing (MassGap.PeriodicStateDLR.wspec hN β Λ) _ _ f
    (MassGap.PeriodicStateDLR.torusState_dlr hN M β Λ S f hf hfit.1 hfit.2)
    (MassGap.PeriodicStateDLR.periodicState_dlr hN β Λ f) hosc

/-- Every box and support fit in every torus past a threshold. -/
theorem boxFits_eventually (Λ S : Finset MassGap.GibbsSpec.ILink) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → BoxFits M Λ S :=
  MassGap.PeriodicStateDLR.exists_inj_bound _ _

/-- **Capacity-free**: one bound, the box kernel spread, for every torus extent past a threshold. -/
theorem torus_local_closing_uniform (hN : N ≠ 0) (β : ℝ) {Λ S : Finset MassGap.GibbsSpec.ILink}
    {f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)} (hf : MassGap.DLRLimit.IsLocalOnC S f)
    {δ : ℝ}
    (hosc : ∀ ω ω', |MassGap.PeriodicStateDLR.wspec hN β Λ f ω
      - MassGap.PeriodicStateDLR.wspec hN β Λ f ω'| ≤ δ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      |MassGap.PeriodicState.torusState hN M β f - MassGap.PeriodicState.periodicState hN β f|
        ≤ δ := by
  obtain ⟨M₀, hM₀⟩ := boxFits_eventually Λ S
  exact ⟨M₀, fun M hM => torus_local_closing hN M β hf (hM₀ M hM) hosc⟩

end Wilson

/-! ## 3. The reference reading -/

section Reading

variable {N : ℕ}

/-- The reference composite in the state `ν`: the reflected and the plain cube field of the reference
pair, each centred by its one-point value in `ν`, multiplied. -/
def refObs (ν : MassGap.DLRLimit.State (Cfg N)) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (k : ℕ) :
    C(Cfg N, ℝ) :=
  ∏ i, smear (dySpacing N k)
    ((pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ) i).1.sub
      (ν (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ) i).1.1)).1
    (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ) i).2

/-- The reading in `σ` is `σ` of the composite centred in `σ`. -/
theorem refReadingS_eq (σ : ℕ → MassGap.DLRLimit.State (Cfg N)) (O : LField (MassGap.SUN.SU N))
    (t ℓ : ℝ) (k : ℕ) : refReadingS σ O t ℓ k = σ k (refObs (σ k) O t ℓ k) := by
  have h1 : Renorm.pref (connectedS σ (fun _ _ => (1 : ℝ))) k
      (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ)) = 1 := by
    simp [Renorm.pref, connectedS]
  unfold refReadingS latSkRS
  rw [h1, one_mul]
  rfl

/-- **The pixel splits** into the two states on the infinite-volume composite, plus the change of
centring inside `σ`. -/
theorem pixel_split (hN : N ≠ 0) (σ : ℕ → MassGap.DLRLimit.State (Cfg N))
    (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (k : ℕ) :
    |ExistenceReduce.refReading hN O t ℓ k - refReadingS σ O t ℓ k|
      ≤ |stateK hN k (refObs (stateK hN k) O t ℓ k) - σ k (refObs (stateK hN k) O t ℓ k)|
        + |σ k (refObs (stateK hN k) O t ℓ k) - σ k (refObs (σ k) O t ℓ k)| := by
  rw [refReading_eq_refReadingS, refReadingS_eq, refReadingS_eq]
  exact abs_sub_le _ _ _

/-- **Decay of boundary influence at the reference composite**: eventually in `k`, a box `Λ` and a
support `S` of the infinite-volume composite that fit in the torus of `stateTD hN c k`, with the box
kernel of the composite spreading by at most `π · √(refMomentS)` over boundary conditions. -/
def BoxPixel (hN : N ≠ 0) (c : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ π : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∃ Λ S : Finset MassGap.GibbsSpec.ILink,
    MassGap.DLRLimit.IsLocalOnC S (refObs (stateK hN k) O t ℓ k)
    ∧ BoxFits (2 * (2 ^ (c + k) - 1) + 1) Λ S
    ∧ ∀ ω ω',
      |MassGap.PeriodicStateDLR.wspec hN (dyBeta (one_le_of_ne_zero hN) k) Λ
          (refObs (stateK hN k) O t ℓ k) ω
        - MassGap.PeriodicStateDLR.wspec hN (dyBeta (one_le_of_ne_zero hN) k) Λ
          (refObs (stateK hN k) O t ℓ k) ω'|
        ≤ π * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k)

/-- **The change of centring inside the torus**: the torus reading of the composite centred in
infinite volume against the one centred in the torus, at most `π · √(refMomentS)`. -/
def CentringPixel (hN : N ≠ 0) (c : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ π : ℝ) : Prop :=
  ∀ᶠ k in atTop,
    |RelativeDecay.stateTD hN c k (refObs (stateK hN k) O t ℓ k)
        - RelativeDecay.stateTD hN c k (refObs (RelativeDecay.stateTD hN c k) O t ℓ k)|
      ≤ π * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k)

/-- **The pixel from boundary influence and centring.** -/
theorem pixelPassage_of_box (hN : N ≠ 0) {c : ℕ} {O : LField (MassGap.SUN.SU N)} {t ℓ π₁ π₂ : ℝ}
    (hB : BoxPixel hN c O t ℓ π₁) (hC : CentringPixel hN c O t ℓ π₂) :
    LightConePassage.PixelPassage hN (RelativeDecay.stateTD hN c) O t ℓ (π₁ + π₂) := by
  filter_upwards [hB, hC] with k hk hc
  obtain ⟨Λ, S, hloc, hfit, hosc⟩ := hk
  have h1 := torus_local_closing hN _ _ hloc hfit hosc
  have h1' : |stateK hN k (refObs (stateK hN k) O t ℓ k)
      - RelativeDecay.stateTD hN c k (refObs (stateK hN k) O t ℓ k)|
      ≤ π₁ * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k) := by
    rw [abs_sub_comm]
    exact h1
  calc |ExistenceReduce.refReading hN O t ℓ k - refReadingS (RelativeDecay.stateTD hN c) O t ℓ k|
      ≤ _ := pixel_split hN (RelativeDecay.stateTD hN c) O t ℓ k
    _ ≤ π₁ * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k)
        + π₂ * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k) :=
        add_le_add h1' hc
    _ = (π₁ + π₂)
        * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k) := by ring

/-- **The pinned path with `hpos` read through boundary influence, centring and the floor** on the
dyadic torus of physical side `2^c · aRun N 1`. -/
theorem clay_canonical_box (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) (c : ℕ) {π₁ π₂ κ : ℝ} (hκ : 0 < κ) (hπ₁ : 0 ≤ π₁) (hπ₂ : 0 ≤ π₂)
    (hπκ : π₁ + π₂ < κ) (hB : BoxPixel hN c O t ℓ π₁) (hC : CentringPixel hN c O t ℓ π₂)
    (hF : LightConePassage.ReadingFloor (RelativeDecay.stateTD hN c) O t ℓ κ)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0 (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  LightConePassage.clay_canonical_lightCone hN2 hN O ht c hκ (add_nonneg hπ₁ hπ₂) hπκ
    (pixelPassage_of_box hN hB hC) hF hD hℓ hW

end Reading

/-! ## 4. The centring is second order in the one-point pixel -/

section Centring

variable {N : ℕ}

/-- The cell weight of a test function at spacing `a`: `∑ₓ a⁴ f(a x)`. -/
def wsum (a : ℝ) (f : TestFn) : ℝ := ∑ᶠ x : MassGap.InfiniteLattice.ISite, a ^ 4 * f.1 (site a x)

theorem wsum_eq {a : ℝ} (ha : 0 < a) {f : TestFn} {R M : ℝ} (hf : IsTest f.1 R M) :
    wsum a f = ∑ x ∈ box ⌈R / a⌉₊, a ^ 4 * f.1 (site a x) := by
  unfold wsum
  refine finsum_eq_sum_of_support_subset _ (fun x hx => ?_)
  refine mem_box_of_ne ha hf x (fun h0 => ?_)
  simp only [Function.mem_support, ne_eq] at hx
  exact hx (by rw [h0, mul_zero])

/-- A smeared field minus a constant is the smeared field minus the constant times the cell weight. -/
theorem smear_sub_eq {a : ℝ} (ha : 0 < a) (O : LField (MassGap.SUN.SU N)) (r : ℝ) (f : TestFn) :
    smear a (O.sub r).1 f = smear a O.1 f - (r * wsum a f) • (1 : C(Cfg N, ℝ)) := by
  obtain ⟨R, M, hf⟩ := f.2
  rw [smear_eq_sum ha _ f hf (Finset.Subset.refl _), smear_eq_sum ha _ f hf (Finset.Subset.refl _),
    wsum_eq ha hf, Finset.mul_sum, Finset.sum_smul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have ht : transObs x (O.sub r).1 = transObs x O.1 - r • (1 : C(Cfg N, ℝ)) := by
    ext U
    simp [transObs_apply, LField.sub]
  rw [ht, smul_sub, smul_smul, mul_comm r]

/-- A translation-invariant state reads a smeared field as the cell weight times the field. -/
theorem state_smear (ν : MassGap.DLRLimit.State (Cfg N))
    (hν : ∀ (x : MassGap.InfiniteLattice.ISite) (F : C(Cfg N, ℝ)), ν (transObs x F) = ν F)
    {a : ℝ} (ha : 0 < a) (F : C(Cfg N, ℝ)) (f : TestFn) :
    ν (smear a F f) = wsum a f * ν F := by
  obtain ⟨R, M, hf⟩ := f.2
  rw [smear_eq_sum ha F f hf (Finset.Subset.refl _), ν.map_sum, wsum_eq ha hf, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ν.map_smul, hν]

/-- The reference composite as the product of its two centred cube fields. -/
theorem refObs_eq (ν : MassGap.DLRLimit.State (Cfg N)) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (k : ℕ) :
    refObs ν O t ℓ k =
      smear (dySpacing N k) ((O.refl 0).sub (ν (O.refl 0).1)).1
          ((ContinuumNontrivial.cubeTest t ℓ).reflect 0)
        * smear (dySpacing N k) (O.sub (ν O.1)).1 (ContinuumNontrivial.cubeTest t ℓ) := by
  have h : ∀ F : Fin 1 ⊕ Fin 1 → SField N,
      (∏ i, smear (dySpacing N k) ((F i).1.sub (ν (F i).1.1)).1 (F i).2)
        = smear (dySpacing N k) ((F (Sum.inl 0)).1.sub (ν (F (Sum.inl 0)).1.1)).1 (F (Sum.inl 0)).2
          * smear (dySpacing N k) ((F (Sum.inr 0)).1.sub (ν (F (Sum.inr 0)).1.1)).1
            (F (Sum.inr 0)).2 := by
    intro F
    rw [Fintype.prod_sum_type, Fin.prod_univ_one, Fin.prod_univ_one]
  exact h (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ))

/-- **The centring identity** in any state: changing the two subtracted constants changes the reading
by the two first-order terms, each a constant times the state's mean of a centred factor, plus the
product of the two changes. -/
theorem centring_identity {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (σ : MassGap.DLRLimit.State X) (A B : C(X, ℝ)) (b₀ b₁ b₀' b₁' : ℝ) :
    σ ((A - b₀ • (1 : C(X, ℝ))) * (B - b₁ • 1)) - σ ((A - b₀' • (1 : C(X, ℝ))) * (B - b₁' • 1))
      = (b₀' - b₀) * σ (B - b₁' • 1) + (b₁' - b₁) * σ (A - b₀' • 1) + (b₀ - b₀') * (b₁ - b₁') := by
  have hexp : ∀ c₀ c₁ : ℝ, (A - c₀ • (1 : C(X, ℝ))) * (B - c₁ • 1)
      = A * B - c₁ • A - c₀ • B + (c₀ * c₁) • 1 := by
    intro c₀ c₁
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul]
    ring
  rw [hexp, hexp]
  simp only [σ.map_add, σ.map_sub, σ.map_smul, σ.map_one]
  ring

/-- **The centring term on the dyadic torus is second order**: it is the product of the two
one-point differences (infinite volume minus torus), of the reflected and the plain field, each
weighted by its cube weight. The torus state is translation invariant (`torusState_shift`), so each
first-order term of `centring_identity` vanishes. -/
theorem centring_eq (hN : N ≠ 0) (c k : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) :
    RelativeDecay.stateTD hN c k (refObs (stateK hN k) O t ℓ k)
        - RelativeDecay.stateTD hN c k (refObs (RelativeDecay.stateTD hN c k) O t ℓ k)
      = (wsum (dySpacing N k) ((ContinuumNontrivial.cubeTest t ℓ).reflect 0)
          * (stateK hN k (O.refl 0).1 - RelativeDecay.stateTD hN c k (O.refl 0).1))
        * (wsum (dySpacing N k) (ContinuumNontrivial.cubeTest t ℓ)
          * (stateK hN k O.1 - RelativeDecay.stateTD hN c k O.1)) := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hσ : ∀ (x : MassGap.InfiniteLattice.ISite) (F : C(Cfg N, ℝ)),
      RelativeDecay.stateTD hN c k (transObs x F) = RelativeDecay.stateTD hN c k F :=
    fun x F => state_transObs (ν := RelativeDecay.stateTD hN c k)
      (fun τ G => MassGap.PeriodicState.torusState_shift hN _ _ τ G) x F
  rw [refObs_eq, refObs_eq, smear_sub_eq ha, smear_sub_eq ha, smear_sub_eq ha, smear_sub_eq ha,
    centring_identity]
  simp only [(RelativeDecay.stateTD hN c k).map_sub, (RelativeDecay.stateTD hN c k).map_smul,
    (RelativeDecay.stateTD hN c k).map_one, state_smear _ hσ ha]
  ring

/-- **The one-point pixels**: eventually in `k`, boxes that fit in the torus of `stateTD hN c k`
around the reflected and the plain single-site field, with box kernel spreads `δ₀`, `δ₁` whose product
with the cube weights is at most `π · √(refMomentS)`. -/
def OnePointPixel (hN : N ≠ 0) (c : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ π : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∃ (Λ₀ S₀ Λ₁ S₁ : Finset MassGap.GibbsSpec.ILink) (δ₀ δ₁ : ℝ),
    MassGap.DLRLimit.IsLocalOnC S₀ (O.refl 0).1
    ∧ BoxFits (2 * (2 ^ (c + k) - 1) + 1) Λ₀ S₀
    ∧ (∀ ω ω', |MassGap.PeriodicStateDLR.wspec hN (dyBeta (one_le_of_ne_zero hN) k) Λ₀ (O.refl 0).1 ω
        - MassGap.PeriodicStateDLR.wspec hN (dyBeta (one_le_of_ne_zero hN) k) Λ₀ (O.refl 0).1 ω'|
        ≤ δ₀)
    ∧ MassGap.DLRLimit.IsLocalOnC S₁ O.1
    ∧ BoxFits (2 * (2 ^ (c + k) - 1) + 1) Λ₁ S₁
    ∧ (∀ ω ω', |MassGap.PeriodicStateDLR.wspec hN (dyBeta (one_le_of_ne_zero hN) k) Λ₁ O.1 ω
        - MassGap.PeriodicStateDLR.wspec hN (dyBeta (one_le_of_ne_zero hN) k) Λ₁ O.1 ω'| ≤ δ₁)
    ∧ |wsum (dySpacing N k) ((ContinuumNontrivial.cubeTest t ℓ).reflect 0)| * δ₀
        * (|wsum (dySpacing N k) (ContinuumNontrivial.cubeTest t ℓ)| * δ₁)
      ≤ π * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k)

/-- **The centring from the one-point pixels.** -/
theorem centringPixel_of_onePoint (hN : N ≠ 0) {c : ℕ} {O : LField (MassGap.SUN.SU N)} {t ℓ π : ℝ}
    (h : OnePointPixel hN c O t ℓ π) : CentringPixel hN c O t ℓ π := by
  filter_upwards [h] with k hk
  obtain ⟨Λ₀, S₀, Λ₁, S₁, δ₀, δ₁, hl₀, hf₀, ho₀, hl₁, hf₁, ho₁, hle⟩ := hk
  have d₀ : |stateK hN k (O.refl 0).1 - RelativeDecay.stateTD hN c k (O.refl 0).1| ≤ δ₀ := by
    rw [abs_sub_comm]
    exact torus_local_closing hN _ _ hl₀ hf₀ ho₀
  have d₁ : |stateK hN k O.1 - RelativeDecay.stateTD hN c k O.1| ≤ δ₁ := by
    rw [abs_sub_comm]
    exact torus_local_closing hN _ _ hl₁ hf₁ ho₁
  rw [centring_eq, abs_mul, abs_mul, abs_mul]
  refine le_trans (mul_le_mul (mul_le_mul_of_nonneg_left d₀ (abs_nonneg _))
    (mul_le_mul_of_nonneg_left d₁ (abs_nonneg _)) (by positivity)
    (mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans d₀))) hle

/-- **The pixel from boundary influence alone**: the box spread of the composite and of the two
one-point fields give `PixelPassage`. -/
theorem pixelPassage_of_boundary (hN : N ≠ 0) {c : ℕ} {O : LField (MassGap.SUN.SU N)}
    {t ℓ π₁ π₂ : ℝ} (hB : BoxPixel hN c O t ℓ π₁) (h1 : OnePointPixel hN c O t ℓ π₂) :
    LightConePassage.PixelPassage hN (RelativeDecay.stateTD hN c) O t ℓ (π₁ + π₂) :=
  pixelPassage_of_box hN hB (centringPixel_of_onePoint hN h1)

/-- **The pinned path with `hpos` read through boundary influence and the floor.** -/
theorem clay_canonical_boundary (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) (c : ℕ) {π₁ π₂ κ : ℝ} (hκ : 0 < κ) (hπ₁ : 0 ≤ π₁) (hπ₂ : 0 ≤ π₂)
    (hπκ : π₁ + π₂ < κ) (hB : BoxPixel hN c O t ℓ π₁) (h1 : OnePointPixel hN c O t ℓ π₂)
    (hF : LightConePassage.ReadingFloor (RelativeDecay.stateTD hN c) O t ℓ κ)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0 (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  clay_canonical_box hN2 hN O ht c hκ hπ₁ hπ₂ hπκ hB (centringPixel_of_onePoint hN h1) hF hD hℓ hW

end Centring

/-! ## 5. Clustering does not close the comparison -/

section Witness

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The point state at `x`. -/
def dirac (x : X) : MassGap.DLRLimit.State X where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  nonneg' _ hf := hf x
  one' := rfl

/-- Under the frozen kernel (`K f = f`) every point state is DLR. -/
theorem dirac_isDLR_frozen (x : X) :
    MassGap.DLRLimit.IsDLR (fun (_ : Unit) (f : C(X, ℝ)) => f) (dirac x) :=
  fun _ _ => rfl

/-- A point state has no connected correlation: it clusters exactly, at every pair. -/
theorem dirac_mul (x : X) (f g : C(X, ℝ)) : dirac x (f * g) = dirac x f * dirac x g := rfl

/-- **`local_closing` is sharp on point states**: the difference is the spread of the kernel. -/
theorem dirac_closing_eq (x y : X) (f : C(X, ℝ)) : |dirac x f - dirac y f| = |f x - f y| := rfl

/-- **Clustering does not close the comparison.** Two DLR states of one specification, each with no
connected correlation at any pair, differ by `1` on an observable with values in `[0, 1]`. -/
theorem clustering_does_not_close :
    ∃ (ν₁ ν₂ : MassGap.DLRLimit.State Bool) (f : C(Bool, ℝ)),
      MassGap.DLRLimit.IsDLR (fun (_ : Unit) (g : C(Bool, ℝ)) => g) ν₁
      ∧ MassGap.DLRLimit.IsDLR (fun (_ : Unit) (g : C(Bool, ℝ)) => g) ν₂
      ∧ (∀ g h : C(Bool, ℝ), ν₁ (g * h) = ν₁ g * ν₁ h)
      ∧ (∀ g h : C(Bool, ℝ), ν₂ (g * h) = ν₂ g * ν₂ h)
      ∧ (∀ b, 0 ≤ f b ∧ f b ≤ 1)
      ∧ |ν₁ f - ν₂ f| = 1 := by
  refine ⟨dirac true, dirac false, ⟨fun b => if b then 1 else 0, continuous_of_discreteTopology⟩,
    dirac_isDLR_frozen true, dirac_isDLR_frozen false, dirac_mul true, dirac_mul false,
    fun b => ?_, ?_⟩
  · cases b <;> norm_num
  · show |(if true = true then (1 : ℝ) else 0) - (if false = true then 1 else 0)| = 1
    norm_num

end Witness

end MassGap.LocalClosing

#print axioms MassGap.LocalClosing.le_of_forall_le
#print axioms MassGap.LocalClosing.ge_of_forall_ge
#print axioms MassGap.LocalClosing.abs_sub_le_of_forall
#print axioms MassGap.LocalClosing.abs_sub_le_of_osc
#print axioms MassGap.LocalClosing.abs_le_of_kernel
#print axioms MassGap.LocalClosing.local_closing
#print axioms MassGap.LocalClosing.torus_local_closing
#print axioms MassGap.LocalClosing.boxFits_eventually
#print axioms MassGap.LocalClosing.torus_local_closing_uniform
#print axioms MassGap.LocalClosing.refReadingS_eq
#print axioms MassGap.LocalClosing.pixel_split
#print axioms MassGap.LocalClosing.pixelPassage_of_box
#print axioms MassGap.LocalClosing.clay_canonical_box
#print axioms MassGap.LocalClosing.wsum_eq
#print axioms MassGap.LocalClosing.smear_sub_eq
#print axioms MassGap.LocalClosing.state_smear
#print axioms MassGap.LocalClosing.refObs_eq
#print axioms MassGap.LocalClosing.centring_identity
#print axioms MassGap.LocalClosing.centring_eq
#print axioms MassGap.LocalClosing.centringPixel_of_onePoint
#print axioms MassGap.LocalClosing.pixelPassage_of_boundary
#print axioms MassGap.LocalClosing.clay_canonical_boundary
#print axioms MassGap.LocalClosing.dirac_isDLR_frozen
#print axioms MassGap.LocalClosing.dirac_mul
#print axioms MassGap.LocalClosing.dirac_closing_eq
#print axioms MassGap.LocalClosing.clustering_does_not_close
