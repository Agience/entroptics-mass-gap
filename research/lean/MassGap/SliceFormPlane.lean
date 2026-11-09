import Mathlib
import MassGap.TorusRefPosPlane

/-!
# MassGap.SliceFormPlane — the slice form of the torus reference vector at the plane plaquette

`TorusRefPosPlane.SliceForm hN M₀ O t ℓ` asks that, eventually in `k`, the cube-smeared connected
field `Y_k = Yv (connectedS (stateT hN M₀) 1) k (refMono O t ℓ)` be a sum of slices
`∑_{r∈R} Qr q r` with `R ⊆ [1, M₀ 2ᵏ]` nonempty and `q` continuous, gauge invariant and nonzero.
This module proves it at `O = planePlaq N`, for `2 ≤ N`, `0 < t`, `0 < ℓ` and
`2(t + ℓ) < M₀ · aRun N 1`.

Write `a = dySpacing N k`, `M′ = M₀ 2ᵏ`, `M = 2M′ + 1` (spatial extent `M + 1`), `c` the torus
expectation of `planePlaq N`.

* `R = [⌈t/a⌉₊, ⌊(t+ℓ)/a⌋₊] ⊆ ℕ`: `n ∈ R ↔ t ≤ a n ≤ t + ℓ`. `B` is the spatial box of slice sites
  with every coordinate in `R`. The cube `[t, t+ℓ]⁴` read at the lattice sites is the image of
  `R × B` under `gS : (r, y) ↦ SliceRPStrict.site r y`, which is injective (`gS_injective`).
* `site_tsh`: below the last site, one transverse step of the slice is one lattice step of `ℤ⁴`,
  `site r (tsh ν y) = e_ν + site r y`; so no plaquette of `B` wraps.
* `planePlaq_site`: the translate of the plane plaquette to `site r y` is the slice plaquette
  `plaqSl e₁ e₂ y` of the spatial links of slice `r` (`SliceRPStrict.readSl`).
* `qPlane M N s c B = ∑_{y∈B} s (plaqSl e₁ e₂ y − c)`, continuous, gauge invariant
  (`TorusRefPosPlane.gaugeInv_plaqSum`); `sum_transObs_eq`: `∑_{y∈B} s T_{site r y}(planePlaq − c)`
  read at `U` is `qPlane (readSl r U)`.
* `sliceForm_planePlaq`: the smear is `∑_{(r,y)∈R×B} a⁴ T_{gS(r,y)}(planePlaq − c)`
  (`ContinuumField.smear` with the cube indicator, support in the image of `gS`), which is
  `∑_{r∈R} Qr (qPlane M N a⁴ c B) r`. The height bound `TorusRefPosProof.eventually_height_le` at
  `D′ = 1` puts `R` in `[1, M′ − 1]`, and `a ≤ ℓ` eventually makes `R` and `B` nonempty. `q ≠ 0`:
  `q (readSl r U)` is `ExistencePosNonnull.planeV a⁴ c (site r '' B) U`, nonzero at some `U`
  (`ExistencePosNonnull.planeV_ne_zero`).
* `clay_canonical_planePlaq_refPassage`: `TorusRefPosPlane.clay_canonical_sliceForm` at
  `O = planePlaq N`: `ClayContinuumPair` from `RefPassage` at some `ε < 1`, `hD` and `hW`.

Classification: with this module, `hpos` (`ExistencePos.LagOnePos`) at the plane plaquette reduces
to `TorusPassageProof.RefPassage` alone, the relative comparison, on one fixed physical
torus and eventually in `k`, of the torus reference reading with the infinite-volume one. This is a reduction, not a discharge.
-/

noncomputable section

namespace MassGap.SliceFormPlane

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.TorusCapstone MassGap.RectWilson MassGap.TorusChain MassGap.TorusRefPosPlane Filter
open scoped Topology

set_option linter.unusedSectionVars false

variable {M N : ℕ}

/-! ## 1. Slice sites and lattice sites -/

/-- The transverse direction `1`. -/
def e₁ : {j : Fin 4 // j ≠ 0} := ⟨1, by decide⟩

/-- The transverse direction `2`. -/
def e₂ : {j : Fin 4 // j ≠ 0} := ⟨2, by decide⟩

/-- One transverse step below the last site raises that coordinate by one. -/
theorem tsh_coord (ν : {j : Fin 4 // j ≠ 0}) (y : TT 0 (Tc M)) (hy : (y ν : ℕ) + 1 < M + 1)
    (j : {j : Fin 4 // j ≠ 0}) :
    ((tsh 0 (Tc M) ν y j : Fin (Tc M j)) : ℕ) = (y j : ℕ) + if j = ν then 1 else 0 := by
  by_cases hj : j = ν
  · subst hj
    have hne : (y j : Fin (M + 1)) ≠ Fin.last M := fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_last] at this
      omega
    rw [if_pos rfl]
    unfold tsh
    rw [Function.update_self]
    exact coe_finRotate_of_ne_last (n := M) hne
  · rw [if_neg hj, add_zero]
    unfold tsh
    rw [Function.update_of_ne hj]

/-- **Below the last site, one transverse step of the slice is one lattice step.** -/
theorem site_tsh (r : ℤ) (ν : {j : Fin 4 // j ≠ 0}) (y : TT 0 (Tc M))
    (hy : (y ν : ℕ) + 1 < M + 1) :
    SliceRPStrict.site (M := M) r (tsh 0 (Tc M) ν y)
      = Function.update (0 : Fin 4 → ℤ) ν.1 1 + SliceRPStrict.site r y := by
  funext i
  by_cases h0 : i = 0
  · subst h0
    have hne : (0 : Fin 4) ≠ ν.1 := fun h => ν.2 h.symm
    simp [SliceRPStrict.site, hne]
  · have hj := tsh_coord ν y hy ⟨i, h0⟩
    simp only [SliceRPStrict.site, dif_neg h0, Pi.add_apply, hj, Function.update_apply]
    by_cases hi : i = ν.1
    · have hs : (⟨i, h0⟩ : {j : Fin 4 // j ≠ 0}) = ν := Subtype.ext hi
      rw [if_pos hs, if_pos hi]
      push_cast
      ring
    · have hs : (⟨i, h0⟩ : {j : Fin 4 // j ≠ 0}) ≠ ν := fun h => hi (congrArg Subtype.val h)
      rw [if_neg hs, if_neg hi]
      simp

theorem ishift_q₀ (μ : Fin 4) :
    GibbsSpec.ishift μ ExistencePosNonnull.q₀.2 = Function.update (0 : Fin 4 → ℤ) μ 1 := by
  funext i
  simp [GibbsSpec.ishift, ExistencePosNonnull.q₀, Function.update_apply]

/-- **The translated plane plaquette is a slice plaquette**, when it does not wrap. -/
theorem planePlaq_site (U : Cfg N) (r : ℤ) (y : TT 0 (Tc M))
    (h1 : (y e₁ : ℕ) + 1 < M + 1) (h2 : (y e₂ : ℕ) + 1 < M + 1) :
    (ExistencePosNonnull.planePlaq N).1 (transConf (SliceRPStrict.site (M := M) r y) U)
      = plaqSl 0 (Tc M) N e₁ e₂ y (SliceRPStrict.readSl r U) := by
  have hA : ExistencePosNonnull.q₀.2 + SliceRPStrict.site (M := M) r y
      = SliceRPStrict.site r y := by
    funext i
    simp [ExistencePosNonnull.q₀]
  have hB : GibbsSpec.ishift 1 ExistencePosNonnull.q₀.2 + SliceRPStrict.site (M := M) r y
      = SliceRPStrict.site r (tsh 0 (Tc M) e₁ y) := by
    rw [ishift_q₀]
    exact (site_tsh r e₁ y h1).symm
  have hC : GibbsSpec.ishift 2 ExistencePosNonnull.q₀.2 + SliceRPStrict.site (M := M) r y
      = SliceRPStrict.site r (tsh 0 (Tc M) e₂ y) := by
    rw [ishift_q₀]
    exact (site_tsh r e₂ y h2).symm
  rw [ExistencePosNonnull.planePlaq_transConf, hA, hB, hC]
  rfl

/-- The lattice site of a time and a slice site. -/
def gS (M : ℕ) (p : ℕ × TT 0 (Tc M)) : Fin 4 → ℤ := SliceRPStrict.site (M := M) (p.1 : ℤ) p.2

theorem gS_zero (p : ℕ × TT 0 (Tc M)) : gS M p 0 = p.1 := SliceRPStrict.site_zero _ _

theorem gS_ne (p : ℕ × TT 0 (Tc M)) {i : Fin 4} (h : i ≠ 0) :
    gS M p i = ((p.2 ⟨i, h⟩ : ℕ) : ℤ) := by
  simp only [gS, SliceRPStrict.site, dif_neg h]

theorem site_injective (r : ℤ) : Function.Injective (SliceRPStrict.site (M := M) r) := by
  intro y y' h
  have := congrArg (TorusChain.perpI M) h
  simpa only [SliceRPStrict.perpI_site] using this

theorem gS_injective : Function.Injective (gS M) := by
  intro p p' h
  have h0 : (p.1 : ℤ) = p'.1 := by
    have := congrFun h 0
    rwa [gS_zero, gS_zero] at this
  have h2 : p.2 = p'.2 := by
    have := congrArg (TorusChain.perpI M) h
    simpa only [gS, SliceRPStrict.perpI_site] using this
  exact Prod.ext (by exact_mod_cast h0) h2

/-! ## 2. The plaquette sum of one slice -/

theorem continuous_plaqSl (y : TT 0 (Tc M)) : Continuous (plaqSl 0 (Tc M) N e₁ e₂ y) := by
  unfold plaqSl
  exact WilsonAction.continuous_wilsonDensity.comp (by fun_prop)

/-- The weighted plaquette sum `∑_{y∈B} s (plaqSl e₁ e₂ y − c)` of one slice. -/
def qPlane (M N : ℕ) (s c : ℝ) (B : Finset (TT 0 (Tc M))) : C(Sl M N, ℝ) :=
  ⟨fun V => ∑ y ∈ B, s * (plaqSl 0 (Tc M) N e₁ e₂ y V - c),
    continuous_finsetSum _ fun y _ =>
      continuous_const.mul ((continuous_plaqSl y).sub continuous_const)⟩

theorem qPlane_apply (s c : ℝ) (B : Finset (TT 0 (Tc M))) (V : Sl M N) :
    qPlane M N s c B V = ∑ y ∈ B, s * (plaqSl 0 (Tc M) N e₁ e₂ y V - c) := rfl

theorem qPlane_gaugeInv (s c : ℝ) (B : Finset (TT 0 (Tc M))) :
    SliceKernelDefinite.GaugeInv ⇑(qPlane M N s c B) :=
  gaugeInv_plaqSum e₁ e₂ B s c

/-- **The plane slice at time `r` reads the slice plaquette sum.** -/
theorem sum_transObs_eq (r : ℤ) (s c : ℝ) (B : Finset (TT 0 (Tc M)))
    (hB : ∀ y ∈ B, (y e₁ : ℕ) + 1 < M + 1 ∧ (y e₂ : ℕ) + 1 < M + 1) (U : Cfg N) :
    (∑ y ∈ B, s • transObs (SliceRPStrict.site (M := M) r y)
        ((ExistencePosNonnull.planePlaq N).sub c).1) U
      = qPlane M N s c B (SliceRPStrict.readSl r U) := by
  rw [ContinuousMap.coe_sum, Finset.sum_apply, qPlane_apply]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [ContinuousMap.smul_apply, smul_eq_mul, transObs_apply,
    ← planePlaq_site U r y (hB y hy).1 (hB y hy).2]
  show s * ((ExistencePosNonnull.planePlaq N).1 (transConf (SliceRPStrict.site r y) U) - c * 1) = _
  rw [mul_one]

/-! ## 3. The slice form at the plane plaquette -/

/-- **`SliceForm` at the plane plaquette.** At `2 ≤ N`, `0 < t`, `0 < ℓ` and
`2(t + ℓ) < M₀ · aRun N 1`, eventually in `k` the torus reference vector is
`∑_{r∈R} Qr (qPlane M N a⁴ c B) r`. -/
theorem sliceForm_planePlaq (hN2 : 2 ≤ N) (hN : N ≠ 0) {M₀ : ℕ} {t ℓ : ℝ} (ht : 0 < t)
    (hℓ : 0 < ℓ) (hM : 2 * (t + ℓ) < M₀ * AsymptoticScaling.aRun N 1) :
    SliceForm hN M₀ (ExistencePosNonnull.planePlaq N) t ℓ := by
  filter_upwards [TorusRefPosProof.eventually_height_le hN (by linarith) hM 1,
    (tendsto_dySpacing N).eventually (ge_mem_nhds hℓ)] with k hk hak
  have ha : 0 < dySpacing N k := dySpacing_pos (one_le_of_ne_zero hN) k
  set a := dySpacing N k with ha_def
  set M' := M₀ * 2 ^ k with hM'
  set c := stateT hN M₀ k (ExistencePosNonnull.planePlaq N).1 with hc
  set F := ((ExistencePosNonnull.planePlaq N).sub c).1 with hF
  set R : Finset ℕ := Finset.Icc ⌈t / a⌉₊ ⌊(t + ℓ) / a⌋₊ with hR
  set B : Finset (TT 0 (Tc (2 * M' + 1))) :=
    Finset.univ.filter (fun y => ∀ j, (y j : ℕ) ∈ R) with hB
  -- the times
  have hmemR : ∀ n : ℕ, n ∈ R ↔ t ≤ a * n ∧ a * n ≤ t + ℓ := by
    intro n
    rw [hR, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff (div_nonneg (by linarith) ha.le),
      div_le_iff₀ ha, le_div_iff₀ ha, mul_comm (n : ℝ) a]
  have hRbd : ∀ n ∈ R, 1 ≤ n ∧ n + 1 ≤ M' := by
    intro n hn
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos n with h | h
      · have := ((hmemR n).mp hn).1
        rw [h, Nat.cast_zero, mul_zero] at this
        linarith
      · exact h
    · have h1 := (Finset.mem_Icc.mp hn).2
      have h2 := Nat.floor_le_ceil ((t + ℓ) / a)
      omega
  have hRne : ⌈t / a⌉₊ ∈ R := by
    rw [hmemR]
    constructor
    · have h := Nat.le_ceil (t / a)
      rw [div_le_iff₀ ha] at h
      linarith [mul_comm a (⌈t / a⌉₊ : ℝ)]
    · have h := Nat.ceil_lt_add_one (div_nonneg ht.le ha.le)
      have h2 : a * (⌈t / a⌉₊ : ℝ) < a * (t / a + 1) := mul_lt_mul_of_pos_left h ha
      have h3 : a * (t / a) = t := mul_div_cancel₀ t ha.ne'
      rw [mul_add, h3, mul_one] at h2
      linarith
  -- the spatial box
  have hBbd : ∀ y ∈ B, (y e₁ : ℕ) + 1 < 2 * M' + 1 + 1 ∧ (y e₂ : ℕ) + 1 < 2 * M' + 1 + 1 := by
    intro y hy
    have h := (Finset.mem_filter.mp hy).2
    have h1 := (hRbd _ (h e₁)).2
    have h2 := (hRbd _ (h e₂)).2
    omega
  set y₀ : TT 0 (Tc (2 * M' + 1)) := fun j => ⟨⌈t / a⌉₊, by
    have := (hRbd _ hRne).2
    show _ < 2 * M' + 1 + 1
    omega⟩ with hy₀_def
  have hy₀ : y₀ ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ => hRne⟩
  -- the cube read at the lattice sites is the image of `R × B`
  have hsurj : ∀ x : Fin 4 → ℤ,
      (ContinuumNontrivial.cubeTest t ℓ).1 (ContinuumField.site a x) ≠ 0 →
        x ∈ (R ×ˢ B).image (gS (2 * M' + 1)) := by
    intro x hx
    have hcube : ∀ i, t ≤ a * (x i : ℝ) ∧ a * (x i : ℝ) ≤ t + ℓ := by
      have hy' : ContinuumNontrivial.cubeInd t ℓ (ContinuumField.site a x) ≠ 0 := hx
      exact Set.mem_of_indicator_ne_zero hy'
    have hpos : ∀ i, 0 ≤ x i := by
      intro i
      have h1 : 0 < a * (x i : ℝ) := lt_of_lt_of_le ht (hcube i).1
      have h2 : (0 : ℝ) < x i := pos_of_mul_pos_right h1 ha.le
      exact_mod_cast h2.le
    have hnat : ∀ i, (((x i).toNat : ℕ) : ℝ) = (x i : ℝ) := by
      intro i
      have : (((x i).toNat : ℕ) : ℤ) = x i := Int.toNat_of_nonneg (hpos i)
      exact_mod_cast this
    have hxR : ∀ i, (x i).toNat ∈ R := fun i => (hmemR _).mpr (by rw [hnat i]; exact hcube i)
    have hlt : ∀ j : {j : Fin 4 // j ≠ 0}, (x j.1).toNat < Tc (2 * M' + 1) j := by
      intro j
      have := (hRbd _ (hxR j.1)).2
      show (x j.1).toNat < 2 * M' + 1 + 1
      omega
    refine Finset.mem_image.mpr ⟨((x 0).toNat, fun j => ⟨(x j.1).toNat, hlt j⟩),
      Finset.mem_product.mpr ⟨hxR 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => hxR j.1⟩⟩,
      ?_⟩
    funext i
    by_cases h : i = 0
    · subst h
      rw [gS_zero]
      exact Int.toNat_of_nonneg (hpos 0)
    · rw [gS_ne _ h]
      exact Int.toNat_of_nonneg (hpos i)
  have hw : ∀ p ∈ R ×ˢ B,
      (ContinuumNontrivial.cubeTest t ℓ).1 (ContinuumField.site a (gS (2 * M' + 1) p)) = 1 := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    refine ContinuumNontrivial.cubeInd_of_mem (fun i => ?_)
    by_cases h : i = 0
    · subst h
      show t ≤ a * ((gS _ p 0 : ℤ) : ℝ) ∧ a * ((gS _ p 0 : ℤ) : ℝ) ≤ t + ℓ
      rw [gS_zero, Int.cast_natCast]
      exact (hmemR _).mp h1
    · show t ≤ a * ((gS _ p i : ℤ) : ℝ) ∧ a * ((gS _ p i : ℤ) : ℝ) ≤ t + ℓ
      rw [gS_ne _ h, Int.cast_natCast]
      exact (hmemR _).mp ((Finset.mem_filter.mp h2).2 _)
  -- the smear as a sum over `R × B`
  have hsm : smear a F (ContinuumNontrivial.cubeTest t ℓ)
      = ∑ p ∈ R ×ˢ B, (a ^ 4) • transObs (gS (2 * M' + 1) p) F := by
    have hsupp : Function.support (fun x : Fin 4 → ℤ =>
        (a ^ 4 * (ContinuumNontrivial.cubeTest t ℓ).1 (ContinuumField.site a x)) • transObs x F)
        ⊆ ↑((R ×ˢ B).image (gS (2 * M' + 1))) := by
      intro x hx
      refine Finset.mem_coe.mpr (hsurj x fun h0 => hx ?_)
      simp only [h0, mul_zero, zero_smul]
    unfold smear
    rw [finsum_eq_sum_of_support_subset _ hsupp,
      Finset.sum_image (by intro p _ p' _ h; exact gS_injective h)]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hw p hp, mul_one]
  have hY : ContinuumCluster.Yv (connectedS (stateT hN M₀) (fun _ _ => 1)) k
      (ExistenceReduce.refMono (ExistencePosNonnull.planePlaq N) t ℓ)
      = smear a F (ContinuumNontrivial.cubeTest t ℓ) := by
    unfold ExistenceReduce.refMono
    rw [ExistencePos.Yv_mono1]
    show (1 : ℝ) • smear a F _ = _
    rw [one_smul]
  refine ⟨R, qPlane (2 * M' + 1) N (a ^ 4) c B,
    fun r hr => ⟨(hRbd r hr).1, by have := (hRbd r hr).2; omega⟩, ⟨_, hRne⟩,
    qPlane_gaugeInv _ _ _, ?_, ?_⟩
  · -- `q ≠ 0`, through the plane slice at time `⌈t/a⌉₊`
    intro hq0
    obtain ⟨U₀, hU₀⟩ := ExistencePosNonnull.planeV_ne_zero hN2 (pow_pos ha 4) c
      (B := B.image (SliceRPStrict.site (M := 2 * M' + 1) ((⌈t / a⌉₊ : ℕ) : ℤ)))
      ⟨_, Finset.mem_image_of_mem _ hy₀⟩
    apply hU₀
    unfold ExistencePosNonnull.planeV
    rw [Finset.sum_image (by intro y _ y' _ h; exact site_injective _ h),
      sum_transObs_eq _ _ _ B hBbd, hq0, ContinuousMap.zero_apply]
  · rw [hY, hsm, Finset.sum_product]
    refine Finset.sum_congr rfl fun r _ => ?_
    ext U
    rw [SliceRPStrict.Qr_apply, ← sum_transObs_eq (r : ℤ) (a ^ 4) c B hBbd U]
    rfl

/-- **The pinned path at the plane plaquette with `hpos` reduced to `RefPassage`.**
`TorusRefPosPlane.clay_canonical_sliceForm` at `O = planePlaq N`, with the slice form supplied by
`sliceForm_planePlaq`: at `2 ≤ N`, `0 < t`, `0 < ℓ`, `2(t + ℓ) < M₀ · aRun N 1`, from
`RefPassage` at some `ε < 1`, `hD` and `hW`. -/
theorem clay_canonical_planePlaq_refPassage (hN2 : 2 ≤ N) (hN : N ≠ 0) {t ℓ : ℝ} (ht : 0 < t)
    (hℓ : 0 < ℓ) {M₀ : ℕ} (hM : 2 * (t + ℓ) < M₀ * AsymptoticScaling.aRun N 1) {ε : ℝ}
    (hε : ε < 1)
    (hR : TorusPassageProof.RefPassage hN M₀ (ExistencePosNonnull.planePlaq N) t ℓ ε)
    (hD : ContinuumSep.DiagBoundSep hN
      (Renorm.connected hN (ExistenceReduce.zCan hN (ExistencePosNonnull.planePlaq N) t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN (ExistencePosNonnull.planePlaq N) t ℓ) 0
      (ExistenceReduce.zCan_refl hN (ExistencePosNonnull.planePlaq N) t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN
        (Renorm.connected hN (ExistenceReduce.zCan hN (ExistencePosNonnull.planePlaq N) t ℓ)) 0
        (Renorm.connected_reflCompat hN
          (ExistenceReduce.zCan hN (ExistencePosNonnull.planePlaq N) t ℓ) 0
          (ExistenceReduce.zCan_refl hN (ExistencePosNonnull.planePlaq N) t ℓ)) hD) (5 * ℓ₀) :=
  clay_canonical_sliceForm hN2 hN _ ht (sliceForm_planePlaq hN2 hN ht hℓ hM) hε hR hD hℓ₀ hW

end MassGap.SliceFormPlane

#print axioms MassGap.SliceFormPlane.tsh_coord
#print axioms MassGap.SliceFormPlane.site_tsh
#print axioms MassGap.SliceFormPlane.ishift_q₀
#print axioms MassGap.SliceFormPlane.planePlaq_site
#print axioms MassGap.SliceFormPlane.gS_injective
#print axioms MassGap.SliceFormPlane.site_injective
#print axioms MassGap.SliceFormPlane.qPlane_gaugeInv
#print axioms MassGap.SliceFormPlane.sum_transObs_eq
#print axioms MassGap.SliceFormPlane.sliceForm_planePlaq
#print axioms MassGap.SliceFormPlane.clay_canonical_planePlaq_refPassage
