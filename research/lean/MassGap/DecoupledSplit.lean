import Mathlib
import MassGap.AnisoTorus

/-!
# MassGap.DecoupledSplit — the decoupled anisotropic torus is a product of 2D tori

At `β_⊥ = 0` the anisotropic Boltzmann weight of `AnisoTorus.ZA` is `e^{−β S_in}`. A link of direction `0` or
`1` at the site `(x₀, x₁, x₂, x₃)` enters only the in-plane plaquettes of the `(0,1)` plane at fixed
`(x₂, x₃)`, and a link of direction `2` or `3` only those of the `(2,3)` plane at fixed `(x₀, x₁)`. This module
builds that splitting and proves `AnisoTorus.DecoupledFactor N β` for every `N` and `β`. Declarations are in
`MassGap.DecoupledSplit`.

* Directions: `Fin 4` is read as a block `bof i = i / 2` and a direction inside the block `kof i = i % 2`;
  `blk b k = 2b + k` is the inverse. A plane is `Plane n = Fin 2 × (Fin 2 → Fin n)`: the block and the two
  transverse coordinates. `embSite b t y` is the 4D site with in-block coordinates `y` and transverse `t`.
* `linkEquiv n : Plane n × TLink 2 n ≃ TLink 4 n`, `(b, t), (k, y) ↦ (blk b k, embSite b t y)`.
* `tshift_embSite`: a step in direction `blk b k` moves only the in-block coordinate `k`, so
  `hol_embP`: the holonomy of the 4D in-plane plaquette `embP p q` is the 2D holonomy of `q` in the
  configuration `l ↦ U (linkEquiv n (p, l))`.
* `sum_inPlane`: `embP` is a bijection of `Plane n × TPlaq 2 n` onto the in-plane plaquettes (the diagonal
  orientations included on both sides), so `sin_split`: `S_in(U) = Σ_p S₂(U_p)`.
* `splitEquiv`: the reindexing by `linkEquiv` followed by currying, a `MeasurableEquiv` from the 4D
  configurations to `Plane n → (2D configurations)`, measure preserving for the product Haar measures
  (`measurePreserving_piCongrLeft`, `Measure.infinitePi_map_curry`, `Measure.infinitePi_eq_pi`).
* `ZA_decoupled`: `ZA N β 0 n = Z₂(β, n) ^ (2 n²)` by Fubini over the planes
  (`integral_fintype_prod_eq_pow`); `decoupledFactor`: `DecoupledFactor N β`, through `Real.log_pow`.
* `decoupled_vanishes_of_twoD`: with the cited `LayerSplit.TwoDCharacter N β` alone, `DA N β 0 · → 0`.

No hypothesis on `N`, `β` or `n` enters: the diagonal plaquettes are matched to the 2D diagonal plaquettes,
so `φ(1) = 0` is not read, and the identity holds at `n = 0` as `1 = 1`.

## What does not follow

`DecoupledFactor` is one of the three inputs of `AnisoTorus.strongEnd_of_aniso`. Of the other two,
`AnisoAnalytic N β` (holomorphy in `β_⊥`, locally bounded uniformly in the window) stays open, and
`WeakMixAnchor N β` follows from the vanishing at `β_⊥ = 0` proved here (`MixAnchor.weakMixAnchor_of_decoupled`).
`LayerSplit.TwoDCharacter N β` remains a cited input.
-/

namespace MassGap.DecoupledSplit

open MeasureTheory Filter Topology MassGap MassGap.LatticeGauge MassGap.TorusDoubling

/-! ## 1. Blocks of directions and plane coordinates -/

/-- The direction `2b + k`: block `b`, direction `k` inside the block. DERIVED: `2` the block size. -/
def blk (b k : Fin 2) : Fin 4 := ⟨2 * b.val + k.val, by have := b.isLt; have := k.isLt; omega⟩

/-- The block of a direction, `i / 2`. DERIVED: `2` the block size. -/
def bof (i : Fin 4) : Fin 2 := ⟨i.val / 2, by have := i.isLt; omega⟩

/-- The direction inside the block, `i % 2`. DERIVED: `2` the block size. -/
def kof (i : Fin 4) : Fin 2 := ⟨i.val % 2, by omega⟩

theorem bof_blk : ∀ b k : Fin 2, bof (blk b k) = b := by decide

theorem kof_blk : ∀ b k : Fin 2, kof (blk b k) = k := by decide

theorem blk_bof_kof : ∀ i : Fin 4, blk (bof i) (kof i) = i := by decide

theorem rev_ne : ∀ b : Fin 2, b.rev ≠ b := by decide

theorem eq_rev_of_ne : ∀ a b : Fin 2, a ≠ b → a = b.rev := by decide

/-- `inPlane (i, j)` is equality of blocks. -/
theorem inPlane_iff : ∀ i j : Fin 4, AnisoTorus.inPlane (i, j) = true ↔ bof j = bof i := by decide

theorem inPlane_blk : ∀ b k₁ k₂ : Fin 2, AnisoTorus.inPlane (blk b k₁, blk b k₂) = true := by decide

/-- **The planes**: a block and the two coordinates transverse to it. DERIVED: `2` the blocks and the
transverse dimension. -/
abbrev Plane (n : ℕ) : Type := Fin 2 × (Fin 2 → Fin n)

/-- `2 n²` planes. DERIVED: `2` the blocks; `n²` the transverse sites. -/
theorem card_plane (n : ℕ) : Fintype.card (Plane n) = 2 * n ^ 2 := by
  simp [Fintype.card_prod]

variable {n : ℕ}

/-- The 4D site with coordinates `y` in block `b` and `t` in the other block. -/
def embSite (b : Fin 2) (t y : Fin 2 → Fin n) : TSite 4 n :=
  fun i => if bof i = b then y (kof i) else t (kof i)

theorem embSite_same (b k : Fin 2) (t y : Fin 2 → Fin n) : embSite b t y (blk b k) = y k := by
  simp [embSite, bof_blk, kof_blk]

theorem embSite_other (b k : Fin 2) (t y : Fin 2 → Fin n) : embSite b t y (blk b.rev k) = t k := by
  simp [embSite, bof_blk, kof_blk, rev_ne]

theorem embSite_eta (x : TSite 4 n) (b : Fin 2) :
    embSite b (fun k => x (blk b.rev k)) (fun k => x (blk b k)) = x := by
  funext j
  dsimp only [embSite]
  split_ifs with h
  · rw [← h, blk_bof_kof]
  · rw [← eq_rev_of_ne _ _ h, blk_bof_kof]

/-- **A step in an in-block direction moves only the in-block coordinate.** -/
theorem tshift_embSite (b k : Fin 2) (t y : Fin 2 → Fin n) :
    tshift (blk b k) (embSite b t y) = embSite b t (tshift k y) := by
  funext j
  unfold tshift
  rw [embSite_same]
  by_cases hj : j = blk b k
  · subst hj
    rw [Function.update_self, embSite_same, Function.update_self]
  · rw [Function.update_of_ne hj]
    by_cases hb : bof j = b
    · have hk : kof j ≠ k := fun hk => hj (by rw [← hb, ← hk, blk_bof_kof])
      simp only [embSite, hb, ↓reduceIte, Function.update_of_ne hk]
    · simp only [embSite, hb, ↓reduceIte]

/-! ## 2. Links and plaquettes -/

variable (n) in
/-- **The link splitting** `Plane n × TLink 2 n ≃ TLink 4 n`. -/
def linkEquiv : Plane n × TLink 2 n ≃ TLink 4 n where
  toFun p := (blk p.1.1 p.2.1, embSite p.1.1 p.1.2 p.2.2)
  invFun l := ((bof l.1, fun k => l.2 (blk (bof l.1).rev k)), (kof l.1, fun k => l.2 (blk (bof l.1) k)))
  left_inv := by
    rintro ⟨⟨b, t⟩, ⟨k, y⟩⟩
    simp only [bof_blk, kof_blk, embSite_same, embSite_other]
  right_inv := by
    rintro ⟨i, x⟩
    exact Prod.ext (blk_bof_kof i) (embSite_eta x (bof i))

/-- The in-plane 4D plaquette of the 2D plaquette `q` in the plane `p`. -/
def embP (p : Plane n) (q : TPlaq 2 n) : TPlaq 4 n :=
  ((blk p.1 q.1.1, blk p.1 q.1.2), embSite p.1 p.2 q.2)

/-- The plane and 2D plaquette of a 4D plaquette (the inverse of `embP` on the in-plane plaquettes). -/
def projP (q : TPlaq 4 n) : Plane n × TPlaq 2 n :=
  ((bof q.1.1, fun k => q.2 (blk (bof q.1.1).rev k)),
    ((kof q.1.1, kof q.1.2), fun k => q.2 (blk (bof q.1.1) k)))

theorem projP_embP (p : Plane n) (q : TPlaq 2 n) : projP (embP p q) = (p, q) := by
  obtain ⟨b, t⟩ := p
  obtain ⟨⟨k₁, k₂⟩, y⟩ := q
  simp only [projP, embP, bof_blk, kof_blk, embSite_same, embSite_other]

theorem embP_projP (q : TPlaq 4 n) (h : AnisoTorus.inPlane q.1 = true) :
    embP (projP q).1 (projP q).2 = q := by
  obtain ⟨⟨i, j⟩, x⟩ := q
  have hj : bof j = bof i := (inPlane_iff i j).1 h
  refine Prod.ext (Prod.ext (blk_bof_kof i) ?_) (embSite_eta x (bof i))
  show blk (bof i) (kof j) = j
  rw [← hj, blk_bof_kof]

/-- **The in-plane plaquette sum is the sum over planes of the 2D plaquette sums** (diagonal orientations
included on both sides). DERIVED: `0` the excluded terms. -/
theorem sum_inPlane (f : TPlaq 4 n → ℝ) :
    ∑ q : TPlaq 4 n, (if AnisoTorus.inPlane q.1 then f q else 0)
      = ∑ p : Plane n, ∑ q : TPlaq 2 n, f (embP p q) := by
  rw [← Finset.sum_filter, ← Fintype.sum_prod_type']
  refine Finset.sum_nbij' projP (fun x => embP x.1 x.2) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact inPlane_blk _ _ _
  · intro q hq
    exact embP_projP q (Finset.mem_filter.1 hq).2
  · rintro ⟨p, q⟩ _
    exact projP_embP p q
  · intro q hq
    exact (congrArg f (embP_projP q (Finset.mem_filter.1 hq).2)).symm

/-! ## 3. Holonomies and the in-plane action -/

section Hol

variable {G : Type} [Group G] [MeasurableSpace G] (φ : G → ℝ)

/-- **The in-plane holonomy is the 2D holonomy** of the plane's configuration. -/
theorem hol_embP (U : TLink 4 n → G) (p : Plane n) (q : TPlaq 2 n) :
    (sysT G 4 n φ).hol (embP p q) U = (sysT G 2 n φ).hol q (fun l => U (linkEquiv n (p, l))) := by
  obtain ⟨b, t⟩ := p
  obtain ⟨⟨k₁, k₂⟩, y⟩ := q
  show (sysT G 4 n φ).hol ((blk b k₁, blk b k₂), embSite b t y) U = _
  rw [hol_eq, hol_eq, tshift_embSite, tshift_embSite]
  rfl

end Hol

/-- **The in-plane action splits over the planes**: `S_in(U) = Σ_p S₂(U_p)`, `U_p l = U (linkEquiv n (p, l))`. -/
theorem sin_split (N : ℕ) (U : (AnisoTorus.sys4 N n).Config) :
    AnisoTorus.Sin N n U
      = ∑ p : Plane n, (sysT (SUN.SU N) 2 n WilsonAction.wilsonDensity).action
          (fun l => U (linkEquiv n (p, l))) := by
  unfold AnisoTorus.Sin
  refine (sum_inPlane (fun q => (AnisoTorus.sys4 N n).φ ((AnisoTorus.sys4 N n).hol q U))).trans ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold System.action
  refine Finset.sum_congr rfl fun q _ => ?_
  show (AnisoTorus.sys4 N n).φ ((sysT (SUN.SU N) 4 n WilsonAction.wilsonDensity).hol (embP p q) U) = _
  rw [hol_embP]
  rfl

/-! ## 4. The measurable splitting and Fubini over the planes -/

section Measure

variable {G : Type} [MeasurableSpace G] (ν : Measure G) [IsProbabilityMeasure ν]

variable (G n) in
/-- **The configuration splitting**: reindex the links by `linkEquiv`, then curry over the planes. -/
noncomputable def splitEquiv : (TLink 4 n → G) ≃ᵐ (Plane n → TLink 2 n → G) :=
  (MeasurableEquiv.piCongrLeft (fun _ : TLink 4 n => G) (linkEquiv n)).symm.trans
    (MeasurableEquiv.curry (Plane n) (TLink 2 n) G)

theorem splitEquiv_apply (U : TLink 4 n → G) (p : Plane n) :
    splitEquiv n G U p = fun l => U (linkEquiv n (p, l)) := rfl

/-- **The splitting preserves the product measure**: `ν` on every 4D link goes to `ν` on every link of
every plane. -/
theorem splitEquiv_measurePreserving :
    MeasurePreserving (splitEquiv n G) (Measure.pi fun _ : TLink 4 n => ν)
      (Measure.pi fun _ : Plane n => Measure.pi fun _ : TLink 2 n => ν) := by
  have h1 : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : TLink 4 n => G) (linkEquiv n))
      (Measure.pi fun _ : Plane n × TLink 2 n => ν) (Measure.pi fun _ : TLink 4 n => ν) :=
    measurePreserving_piCongrLeft (μ := fun _ : TLink 4 n => ν) (linkEquiv n)
  have hmap := Measure.infinitePi_map_curry (X := G) (ι := Plane n) (κ := TLink 2 n) (fun _ _ => ν)
  simp only [Measure.infinitePi_eq_pi] at hmap
  have h2 : MeasurePreserving (MeasurableEquiv.curry (Plane n) (TLink 2 n) G)
      (Measure.pi fun _ : Plane n × TLink 2 n => ν)
      (Measure.pi fun _ : Plane n => Measure.pi fun _ : TLink 2 n => ν) :=
    ⟨(MeasurableEquiv.curry (Plane n) (TLink 2 n) G).measurable, hmap⟩
  exact h2.comp (MeasurePreserving.symm _ h1)

end Measure

/-- **The decoupled partition function**: `ZA(β, 0, n) = Z₂(β, n) ^ (2 n²)`. DERIVED: `0` the decoupled end;
`2 n²` the planes. -/
theorem ZA_decoupled (N : ℕ) (β : ℝ) (n : ℕ) :
    AnisoTorus.ZA N β 0 n = (ZT (SUN.SU N) 2 WilsonAction.wilsonDensity β n) ^ (2 * n ^ 2) := by
  have hpt : ∀ U : (AnisoTorus.sys4 N n).Config,
      Real.exp (-(β * AnisoTorus.Sin N n U + 0 * AnisoTorus.Smix N n U))
        = (fun V : Plane n → TLink 2 n → SUN.SU N =>
            ∏ p, (sysT (SUN.SU N) 2 n WilsonAction.wilsonDensity).boltz β (V p))
          (splitEquiv n (SUN.SU N) U) := by
    intro U
    rw [zero_mul, add_zero, sin_split, Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
    simp only [splitEquiv_apply, System.boltz, neg_mul]
    rfl
  have hmp := splitEquiv_measurePreserving (n := n) (CompactGauge.probHaar (SUN.SU N))
  calc AnisoTorus.ZA N β 0 n
      = ∫ U, (fun V : Plane n → TLink 2 n → SUN.SU N =>
            ∏ p, (sysT (SUN.SU N) 2 n WilsonAction.wilsonDensity).boltz β (V p))
          (splitEquiv n (SUN.SU N) U)
          ∂(Measure.pi fun _ : TLink 4 n => CompactGauge.probHaar (SUN.SU N)) := by
        unfold AnisoTorus.ZA
        exact integral_congr_ae (Eventually.of_forall hpt)
    _ = ∫ V, ∏ p, (sysT (SUN.SU N) 2 n WilsonAction.wilsonDensity).boltz β (V p)
          ∂(Measure.pi fun _ : Plane n =>
            Measure.pi fun _ : TLink 2 n => CompactGauge.probHaar (SUN.SU N)) :=
        hmp.integral_comp' (fun V : Plane n → TLink 2 n → SUN.SU N =>
          ∏ p, (sysT (SUN.SU N) 2 n WilsonAction.wilsonDensity).boltz β (V p))
    _ = (∫ v, (sysT (SUN.SU N) 2 n WilsonAction.wilsonDensity).boltz β v
          ∂(Measure.pi fun _ : TLink 2 n => CompactGauge.probHaar (SUN.SU N)))
            ^ Fintype.card (Plane n) :=
        integral_fintype_prod_eq_pow _
    _ = _ := by
      rw [card_plane]
      rfl

/-- **`DecoupledFactor N β` holds**: `log ZA(β, 0, n) = 2 n² log Z₂(β, n)`, for every `N` and `β`. DERIVED:
`0` the decoupled end; `2 n²` the planes. -/
theorem decoupledFactor (N : ℕ) (β : ℝ) : AnisoTorus.DecoupledFactor N β := by
  intro n _
  unfold AnisoTorus.logZA LayerSplit.logZ2
  rw [ZA_decoupled, Real.log_pow]
  push_cast
  ring

/-- **The decoupled end vanishes on the cited 2D character expansion alone**: `TwoDCharacter N β` gives
`DA N β 0 · → 0`. DERIVED: `0` the decoupled end and the limit. -/
theorem decoupled_vanishes_of_twoD {N : ℕ} {β : ℝ} (hC : LayerSplit.TwoDCharacter N β) :
    Tendsto (fun w => AnisoTorus.DA N β 0 w) atTop (𝓝 0) :=
  AnisoTorus.decoupled_vanishes (decoupledFactor N β) hC

end MassGap.DecoupledSplit

#print axioms MassGap.DecoupledSplit.linkEquiv
#print axioms MassGap.DecoupledSplit.tshift_embSite
#print axioms MassGap.DecoupledSplit.sum_inPlane
#print axioms MassGap.DecoupledSplit.hol_embP
#print axioms MassGap.DecoupledSplit.sin_split
#print axioms MassGap.DecoupledSplit.splitEquiv_measurePreserving
#print axioms MassGap.DecoupledSplit.ZA_decoupled
#print axioms MassGap.DecoupledSplit.decoupledFactor
#print axioms MassGap.DecoupledSplit.decoupled_vanishes_of_twoD
