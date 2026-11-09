import Mathlib
import MassGap.RelativeDecay
import MassGap.ContinuumHypercubic

noncomputable section

/-!
# MassGap.LightConePassage — the light cone rotated into space, the pixel, and `hpos` from both

## 1. The light cone rotated into space (proved)

The relabelling `iaxisObs e` of `ContinuumHypercubic` intertwines the reflections and shifts:

* `iaxisSite_ireflSite`, `iaxisConf_ireflConf`, `iaxisObs_ireflObs`:
  `iaxisObs e ∘ ireflObs τ c = ireflObs (e τ) c ∘ iaxisObs e`;
* `iaxisConf_ishiftConf`, `iaxisObs_ishiftObsL`, `iaxisObs_iterate_shift`: the same for the unit
  shift along `τ` and its iterates;
* `iaxisObs_mem`: it carries `gaugeInvHalfSpaceAlg τ c` into `gaugeInvHalfSpaceAlg (e τ) c`.

With `ContinuumHypercubic.torusState_axis`, `torusConn_axis` reads the torus pairing along `τ` as the
pairing along `e τ` of the relabelled observable, so `fixedWindowDecay_perm` and
`fixedWindowDecay_dir` carry `WeakCouplingWindow.FixedWindowDecay` from the time direction to every
direction. `relDecay_of_WDelta2_dir`: from `WDelta2`, along every direction `τ` (spatial ones
included), eventually in `k` the transfer data `DkDir hN τ k` of the infinite-volume state has a rate
`r > 0` with `rⁿ ≤ exp(−(c/(5ℓ₀)) · dySpacing N k · n)` and `RelativeDecay.RelDecayAt` at `r`: decay
relative to the reading itself, along space as along time.

## 2. Capacity is unbounded, the pixel is not (proved, witness)

`n` independent two-level sites, each with excited weight `q` over the closed chain (`q = μᴸ` for the
kernel `diag(1, μ)` of `RelativeDecay.wK` and closed length `L`):

* `capZ_eq`: the closed-chain weight is `(1 + q)ⁿ`; `capExcited_ge`: the global excited weight
  `(1 + q)ⁿ − 1` is at least `n q`, unbounded in the capacity `n`;
* `capZX_eq`, `capRead_eq`: the reading of the excited projector at one site is `q/(1 + q)` at every
  `n`; its vacuum reading is `0`, so the reading departs from the vacuum by `q/(1 + q) ≤ q`
  (`capRead_le`), independent of `n`.

The excited weight `s = hs(r^{∗m})/|c|^{2(m+1)}` of `RelativeDecay.Zh_close_rel` is the global one. On
a slice whose transverse extent grows it grows with the slice, while a local reading departs from the
vacuum by a pixel fixed by the distance alone. A capacity-uniform comparison of a torus with the
infinite volume therefore has to be measured on the reading's light cone, not by `s`.

## 3. `hpos` from the pixel and a floor (proved)

`refMomentS σ O t ℓ k` is the second moment `σ((θΦ Φ)²)` of the reflected reference pair (the
four-fold family `θΦ, Φ, θΦ, Φ`), the scale `Zh_close_rel` measures its closing error by.

* `PixelPassage hN σ O t ℓ π`: eventually `|refReading − refReadingS σ| ≤ π · √(refMomentS σ)`: (1b),
  the infinite-volume reading against the reading in `σ`, relative to the second moment.
* `ReadingFloor σ O t ℓ κ`: eventually `0 < refReadingS σ` and `κ · √(refMomentS σ) ≤ refReadingS σ`:
  (1a), the reading against its own second moment.
* `rel_of_pixel_floor`: the two give `|R − R_σ| ≤ (π/κ) · R_σ`.
* `hpos_of_pixel_floor`: at `0 ≤ π < κ` they give the pinned `hpos`;
  `clay_canonical_pixel` is `ExistenceReduce.clay_canonical` with `hpos` so replaced;
  `clay_canonical_lightCone` is that at the dyadic torus `RelativeDecay.stateTD hN c` of physical side
  `2^c · aRun N 1`.

## What stays open

(1b) is not proved. On `stateTD hN c` the pixel is expected to be `exp(−m · 2^c · aRun N 1)` up to a
constant, for `m` the physical gap of `relDecay_of_WDelta2_dir`, so fixed in `k` and small at large
`c` (argued). The tree has no step that produces it: `Zh_close_rel` compares a trace with the vacuum of
the same slice, with the global weight `s`; comparing a cubic torus of side `L` with the
infinite volume one direction at a time passes through slices of transverse extent `L' → ∞`, where `s`
is unbounded (section 2), and the tree has no rectangular torus states (`RectWilson.ZR` is a partition
function only). (1a) is not proved either.
-/

namespace MassGap.LightConePassage

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.TorusCapstone MassGap.TransferGap MassGap.ContinuumHypercubic MassGap.LatticeReflection
  MassGap.InfiniteShift MassGap.ReflectionShift MassGap.HalfSpaceAlgebra MassGap.GaugeInvariantAlgebra
  Filter

/-! ## 1. The light cone rotated into space -/

section Rotation

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]

/-- The relabelling carries the reflection in `τ` to the reflection in `e τ`, on sites. -/
theorem iaxisSite_ireflSite (e : Equiv.Perm (Fin 4)) (τ : Fin 4) (c : ℤ) (x : ISite) :
    iaxisSite e (ireflSite τ c x) = ireflSite (e τ) c (iaxisSite e x) := by
  funext j
  by_cases h : j = e τ
  · subst h
    simp [iaxisSite, ireflSite]
  · have h' : e.symm j ≠ τ := fun hc => h (by rw [← hc, Equiv.apply_symm_apply])
    simp only [iaxisSite, ireflSite, Function.update_of_ne h, Function.update_of_ne h']

omit [TopologicalSpace G] [ContinuousInv G] [CompactSpace G] in
/-- The relabelling carries the reflection in `τ` to the reflection in `e τ`, on configurations. -/
theorem iaxisConf_ireflConf (e : Equiv.Perm (Fin 4)) (τ : Fin 4) (c : ℤ) (U : IConf G) :
    ireflConf τ c (iaxisConf e U) = iaxisConf e (ireflConf (e τ) c U) := by
  funext l
  by_cases h : l.1 = τ
  · have h' : e l.1 = e τ := by rw [h]
    simp only [ireflConf, iaxisConf, iaxisLink, ireflLink, if_pos h, if_pos h', iaxisSite_ireflSite]
  · have h' : e l.1 ≠ e τ := fun hc => h (e.injective hc)
    simp only [ireflConf, iaxisConf, iaxisLink, ireflLink, if_neg h, if_neg h', iaxisSite_ireflSite]

/-- **The relabelling intertwines the reflections**: `iaxisObs e ∘ ireflObs τ c = ireflObs (e τ) c ∘
iaxisObs e`. -/
theorem iaxisObs_ireflObs (e : Equiv.Perm (Fin 4)) (τ : Fin 4) (c : ℤ) (F : C(IConf G, ℝ)) :
    iaxisObs e (ireflObs τ c F) = ireflObs (e τ) c (iaxisObs e F) := by
  ext U
  show F (ireflConf τ c (iaxisConf e U)) = F (iaxisConf e (ireflConf (e τ) c U))
  rw [iaxisConf_ireflConf]

omit [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G] in
/-- The relabelling carries the shift along `τ` to the shift along `e τ`, on configurations. -/
theorem iaxisConf_ishiftConf (e : Equiv.Perm (Fin 4)) (τ : Fin 4) (U : IConf G) :
    ishiftConf τ (iaxisConf e U) = iaxisConf e (ishiftConf (e τ) U) := by
  funext l
  show U (iaxisLink e (ishiftLink τ l)) = U (ishiftLink (e τ) (iaxisLink e l))
  simp only [iaxisLink, ishiftLink, ishift_iaxisSite]

/-- **The relabelling intertwines the shifts.** -/
theorem iaxisObs_ishiftObsL (e : Equiv.Perm (Fin 4)) (τ : Fin 4) (F : C(IConf G, ℝ)) :
    iaxisObs e (ishiftObsL τ F) = ishiftObsL (e τ) (iaxisObs e F) := by
  ext U
  show F (ishiftConf τ (iaxisConf e U)) = F (iaxisConf e (ishiftConf (e τ) U))
  rw [iaxisConf_ishiftConf]

theorem iaxisObs_iterate_shift (e : Equiv.Perm (Fin 4)) (τ : Fin 4) (n : ℕ) (F : C(IConf G, ℝ)) :
    iaxisObs e ((⇑(ishiftObsL τ))^[n] F) = (⇑(ishiftObsL (e τ)))^[n] (iaxisObs e F) := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, iaxisObs_ishiftObsL]

/-- The relabelling carries the positive half-space along `τ` into the one along `e τ`. -/
theorem iaxisLink_mem_posHalf (e : Equiv.Perm (Fin 4)) {τ : Fin 4} {c : ℤ} {l : ILink}
    (hl : l ∈ posHalf τ c) : iaxisLink e l ∈ posHalf (e τ) c := by
  show c ≤ iaxisSite e l.2 (e τ)
  simp only [iaxisSite, Equiv.symm_apply_apply]
  exact hl

/-- **The relabelling carries the gauge-invariant half-space algebra along `τ` into the one along
`e τ`.** -/
theorem iaxisObs_mem (e : Equiv.Perm (Fin 4)) {τ : Fin 4} {c : ℤ} {F : C(IConf G, ℝ)}
    (hF : F ∈ gaugeInvHalfSpaceAlg (G := G) τ c) :
    iaxisObs e F ∈ gaugeInvHalfSpaceAlg (G := G) (e τ) c := by
  obtain ⟨⟨S, hS, hloc⟩, hg⟩ := hF
  refine ⟨⟨S.image (iaxisLink e), ?_, isLocalOn_iaxisObs e hloc⟩, isIGaugeInvariant_iaxisObs hg e⟩
  intro l hl
  obtain ⟨l', hl', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hl)
  exact iaxisLink_mem_posHalf e (hS (Finset.mem_coe.mpr hl'))

end Rotation

section RotationTorus

variable {N : ℕ}

/-- **The torus pairing along `τ` is the pairing along `e τ` of the relabelled observable.** -/
theorem torusConn_axis (hN : N ≠ 0) (e : Equiv.Perm (Fin 4)) (τ : Fin 4) (p : ℤ) (β : ℝ) (j : ℕ)
    (x : C(IConf (MassGap.SUN.SU N), ℝ)) (m : ℕ) :
    PeriodicReduce.torusConn (e τ) p hN β j (iaxisObs e x) m
      = PeriodicReduce.torusConn τ p hN β j x m := by
  unfold PeriodicReduce.torusConn
  rw [← iaxisObs_ireflObs, ← iaxisObs_iterate_shift, ← iaxisObs_mul]
  simp only [torusState_axis]

/-- **`FixedWindowDecay` moves along a relabelling of the axes.** -/
theorem fixedWindowDecay_perm (hN : N ≠ 0) (e : Equiv.Perm (Fin 4)) {τ : Fin 4} {p : ℤ} {L : ℝ}
    (h : WeakCouplingWindow.FixedWindowDecay (e τ) p hN L) :
    WeakCouplingWindow.FixedWindowDecay τ p hN L := by
  obtain ⟨q, hq0, hq1, hev⟩ := h
  refine ⟨q, hq0, hq1, ?_⟩
  filter_upwards [hev] with β hβ
  obtain ⟨m, hm, hmL, hx⟩ := hβ
  refine ⟨m, hm, hmL, fun x hxm ε hε => ?_⟩
  filter_upwards [hx (iaxisObs e x) (iaxisObs_mem e hxm) ε hε] with j hj
  rwa [torusConn_axis, torusConn_axis] at hj

/-- **`FixedWindowDecay` along the time direction gives it along every direction.** -/
theorem fixedWindowDecay_dir (hN : N ≠ 0) (τ : Fin 4) {p : ℤ} {L : ℝ}
    (h : WeakCouplingWindow.FixedWindowDecay 0 p hN L) :
    WeakCouplingWindow.FixedWindowDecay τ p hN L :=
  fixedWindowDecay_perm hN (Equiv.swap τ 0) (by rw [Equiv.swap_apply_left]; exact h)

/-- The transfer data of step `k` along the direction `τ`. -/
abbrev DkDir (hN : N ≠ 0) (τ : Fin 4) (k : ℕ) :
    Transfer.TransferData
      ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0) :=
  ContinuumCluster.DkAlong hN (dyBeta (one_le_of_ne_zero hN)) τ k

/-- **The relative gap from `WDelta2` along every direction.** Spatial directions included: the
transfer along `τ` decays relative to the reading itself at the same physical rate. -/
theorem relDecay_of_WDelta2_dir (hN2 : 2 ≤ N) (hN : N ≠ 0) (τ : Fin 4) {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀)
    (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∃ r : ℝ, 0 < r ∧
      (∀ n : ℕ, r ^ n ≤ Real.exp (-(c / (5 * ℓ₀) * (dySpacing N k * n)))) ∧
      RelativeDecay.RelDecayAt (DkDir hN τ k) r := by
  obtain ⟨c, hc, hT⟩ := ContinuumCluster.towerGapAt_dyBeta_of_fixedWindowDecay hN2 hN τ
    (by positivity : (0 : ℝ) < 5 * ℓ₀)
    (fixedWindowDecay_dir hN τ (DoublingClay2.fixedWindowDecay_of_WDelta2 hN hℓ hW))
  refine ⟨c, hc, ?_⟩
  filter_upwards [hT] with k hk
  obtain ⟨r, hr, hg, hrate⟩ := hk
  exact ⟨r, hr, fun n => RelativeDecay.pow_le_exp_of_log hr hrate n,
    RelativeDecay.relDecayAt_of_gapAt _ hr.le hg⟩

end RotationTorus

/-! ## 2. Capacity is unbounded, the pixel is not -/

section Capacity

/-- The closed-chain weight of `n` independent two-level sites, excited weight `q` per site. -/
def capZ (q : ℝ) (n : ℕ) : ℝ := ∑ s : Fin n → Fin 2, ∏ i, q ^ (s i : ℕ)

/-- The same weight with the excited projector inserted at site `0` of `n + 1` sites. -/
def capZX (q : ℝ) (n : ℕ) : ℝ :=
  ∑ s : Fin (n + 1) → Fin 2, ((s 0 : ℕ) : ℝ) * ∏ i, q ^ (s i : ℕ)

/-- The reading of the excited projector at one site of `n + 1`. -/
def capRead (q : ℝ) (n : ℕ) : ℝ := capZX q n / capZ q (n + 1)

theorem capZ_eq (q : ℝ) (n : ℕ) : capZ q n = (1 + q) ^ n := by
  unfold capZ
  rw [← Fintype.prod_sum (fun (_ : Fin n) (j : Fin 2) => q ^ (j : ℕ))]
  simp [Fin.sum_univ_two]

theorem capZX_eq (q : ℝ) (n : ℕ) : capZX q n = q * (1 + q) ^ n := by
  have h : ∀ s : Fin (n + 1) → Fin 2, ((s 0 : ℕ) : ℝ) * ∏ i, q ^ (s i : ℕ)
      = ∏ i, (if i = 0 then ((s i : ℕ) : ℝ) * q ^ (s i : ℕ) else q ^ (s i : ℕ)) := by
    intro s
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [Fin.succ_ne_zero, ↓reduceIte]
    ring
  unfold capZX
  simp_rw [h]
  rw [← Fintype.prod_sum (fun (i : Fin (n + 1)) (j : Fin 2) =>
    if i = 0 then ((j : ℕ) : ℝ) * q ^ (j : ℕ) else q ^ (j : ℕ))]
  rw [Fin.prod_univ_succ]
  simp only [Fin.succ_ne_zero, ↓reduceIte, Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
    Nat.cast_zero, Nat.cast_one, pow_zero, pow_one, zero_mul, one_mul,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- **The pixel does not depend on the capacity**: the one-site reading is `q/(1 + q)` at every `n`. -/
theorem capRead_eq {q : ℝ} (hq : 0 ≤ q) (n : ℕ) : capRead q n = q / (1 + q) := by
  have h1 : (0 : ℝ) < 1 + q := by linarith
  unfold capRead
  rw [capZX_eq, capZ_eq, pow_succ]
  field_simp

theorem capRead_le {q : ℝ} (hq : 0 ≤ q) (n : ℕ) : capRead q n ≤ q := by
  rw [capRead_eq hq, div_le_iff₀ (by linarith)]
  nlinarith

/-- **The global excited weight grows with the capacity**: `(1 + q)ⁿ − 1 ≥ n q`. -/
theorem capExcited_ge {q : ℝ} (hq : 0 ≤ q) (n : ℕ) : (n : ℝ) * q ≤ capZ q n - 1 := by
  rw [capZ_eq]
  have := one_add_mul_le_pow (show (-2 : ℝ) ≤ q by linarith) n
  linarith

end Capacity

/-! ## 3. `hpos` from the pixel and a floor -/

section Assembly

variable {N : ℕ}

/-- The second moment `σ((θΦ Φ)²)` of the reflected reference pair at unit field strength. -/
def refMomentS (σ : ℕ → MassGap.DLRLimit.State (Cfg N)) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (k : ℕ) : ℝ :=
  latSkRS σ (connectedS σ (fun _ _ => 1)) k
    (Sum.elim (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ))
      (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ)))

/-- **(1b), the pixel**: the infinite-volume reference reading against the reading in `σ`, relative
to the second moment in `σ`. -/
def PixelPassage (hN : N ≠ 0) (σ : ℕ → MassGap.DLRLimit.State (Cfg N))
    (O : LField (MassGap.SUN.SU N)) (t ℓ π : ℝ) : Prop :=
  ∀ᶠ k in atTop, |ExistenceReduce.refReading hN O t ℓ k - refReadingS σ O t ℓ k|
    ≤ π * Real.sqrt (refMomentS σ O t ℓ k)

/-- **(1a), the floor**: the reading in `σ` is positive and at least `κ` times the square root of its
second moment. -/
def ReadingFloor (σ : ℕ → MassGap.DLRLimit.State (Cfg N)) (O : LField (MassGap.SUN.SU N))
    (t ℓ κ : ℝ) : Prop :=
  ∀ᶠ k in atTop, 0 < refReadingS σ O t ℓ k
    ∧ κ * Real.sqrt (refMomentS σ O t ℓ k) ≤ refReadingS σ O t ℓ k

/-- **The pixel against the floor is a relative bound**: `|R − R_σ| ≤ π Q` and `κ Q ≤ R_σ` give
`|R − R_σ| ≤ (π/κ) R_σ`. -/
theorem rel_of_pixel_floor {R Rσ Q π κ : ℝ} (hκ : 0 < κ) (hπ : 0 ≤ π)
    (h1 : |R - Rσ| ≤ π * Q) (h2 : κ * Q ≤ Rσ) : |R - Rσ| ≤ π / κ * Rσ := by
  have e : π * Q = π / κ * (κ * Q) := by field_simp
  calc |R - Rσ| ≤ π * Q := h1
    _ = π / κ * (κ * Q) := e
    _ ≤ π / κ * Rσ := mul_le_mul_of_nonneg_left h2 (div_nonneg hπ hκ.le)

/-- **`hpos` from the pixel and the floor**, at `0 ≤ π < κ`. -/
theorem hpos_of_pixel_floor (hN : N ≠ 0) (σ : ℕ → MassGap.DLRLimit.State (Cfg N))
    (O : LField (MassGap.SUN.SU N)) {t ℓ π κ : ℝ} (hκ : 0 < κ) (hπ : 0 ≤ π) (hπκ : π < κ)
    (hP : PixelPassage hN σ O t ℓ π) (hF : ReadingFloor σ O t ℓ κ) :
    ∀ᶠ k in atTop, 0 < ExistenceReduce.refReading hN O t ℓ k :=
  RelativeDecay.hpos_of_relS hN σ O (ε := π / κ) ((div_lt_one hκ).mpr hπκ)
    (hF.mono fun _ hk => hk.1)
    (by
      filter_upwards [hP, hF] with k h1 h2
      exact rel_of_pixel_floor hκ hπ h1 h2.2)

/-- **The pinned path with `hpos` read through the pixel and the floor in any per-step state.** -/
theorem clay_canonical_pixel (hN2 : 2 ≤ N) (hN : N ≠ 0) (σ : ℕ → MassGap.DLRLimit.State (Cfg N))
    (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ} (ht : 0 < t) {π κ : ℝ} (hκ : 0 < κ) (hπ : 0 ≤ π)
    (hπκ : π < κ) (hP : PixelPassage hN σ O t ℓ π) (hF : ReadingFloor σ O t ℓ κ)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0 (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  ExistenceReduce.clay_canonical hN2 hN O ht (hpos_of_pixel_floor hN σ O hκ hπ hπκ hP hF) hD hℓ hW

/-- **The pinned path with `hpos` read on the dyadic torus of physical side `2^c · aRun N 1`.** -/
theorem clay_canonical_lightCone (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) (c : ℕ) {π κ : ℝ} (hκ : 0 < κ) (hπ : 0 ≤ π) (hπκ : π < κ)
    (hP : PixelPassage hN (RelativeDecay.stateTD hN c) O t ℓ π)
    (hF : ReadingFloor (RelativeDecay.stateTD hN c) O t ℓ κ)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0 (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  clay_canonical_pixel hN2 hN (RelativeDecay.stateTD hN c) O ht hκ hπ hπκ hP hF hD hℓ hW

end Assembly

end MassGap.LightConePassage

#print axioms MassGap.LightConePassage.iaxisSite_ireflSite
#print axioms MassGap.LightConePassage.iaxisConf_ireflConf
#print axioms MassGap.LightConePassage.iaxisObs_ireflObs
#print axioms MassGap.LightConePassage.iaxisConf_ishiftConf
#print axioms MassGap.LightConePassage.iaxisObs_ishiftObsL
#print axioms MassGap.LightConePassage.iaxisObs_iterate_shift
#print axioms MassGap.LightConePassage.iaxisLink_mem_posHalf
#print axioms MassGap.LightConePassage.iaxisObs_mem
#print axioms MassGap.LightConePassage.torusConn_axis
#print axioms MassGap.LightConePassage.fixedWindowDecay_perm
#print axioms MassGap.LightConePassage.fixedWindowDecay_dir
#print axioms MassGap.LightConePassage.relDecay_of_WDelta2_dir
#print axioms MassGap.LightConePassage.capZ_eq
#print axioms MassGap.LightConePassage.capZX_eq
#print axioms MassGap.LightConePassage.capRead_eq
#print axioms MassGap.LightConePassage.capRead_le
#print axioms MassGap.LightConePassage.capExcited_ge
#print axioms MassGap.LightConePassage.rel_of_pixel_floor
#print axioms MassGap.LightConePassage.hpos_of_pixel_floor
#print axioms MassGap.LightConePassage.clay_canonical_pixel
#print axioms MassGap.LightConePassage.clay_canonical_lightCone
