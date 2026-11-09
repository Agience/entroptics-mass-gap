import Mathlib
import MassGap.ElectricExactProof
import MassGap.GapSideTwistBridge
import MassGap.TwistDeficitUnionN

/-!
# MassGap.GapSideVortexAntiDiagonal — the 't Hooft sheet survives the moved-torus decimation with the same constant, so the vortex free energy has an exact anti-diagonal

The flat Migdal–Kadanoff chain `W_{i+1} = ν π (μ π)² ((w ⋆ w) ⋆ (w ⋆ w))`, `w = W_i(½ Re tr ·)⁴`, is the
moved-torus decimation of the side-`2n` torus to the side-`n` torus (`ElectricExactProof.electricExact`). This
module runs the same decimation on the torus twisted by the centre sheet `GapSideTwistFlat.sheet a b (−1)`
(`−1` on the `(a, b)` and `(b, a)` plaquettes at `x_a = x_b = 0`).

## The objects

* `Ztw C i P n`: the side-`n` torus with weight `W_i` on each plaquette, twisted by the sheet in the plane `P`.
  `Zmktw C i P n`: the same after the bond moves of every direction (`HolderBondMoving.mkField`).
* `holderExcessTw C i P m = log Zmktw − log Ztw`, the twisted twin of `ElectricStepChain.holderExcess`.
* `vortexF C i P n = −log(Ztw C i P n / Zh C i n)`, the vortex free energy of the chain torus.

## What is proved

* `conv_centre_shift`: `(u(z ·) ⋆ v)(g) = (u ⋆ v)(z g)` for every `z` (left invariance of Haar measure), and
  `K4_centre_shift`: `((w(z ·) ⋆ w) ⋆ (w ⋆ w))(g) = ((w ⋆ w) ⋆ (w ⋆ w))(z g)`.
* `decimation_twist`: for every compact group, every continuous class `w` and every group-valued pattern
  `τ` on the coarse plaquettes, the side-`2n` blocks with `τ_{X,p}` multiplied into the first fine plaquette of
  the block `(X, p)` decimate to the side-`n` torus with `τ_{X,p}` multiplied into the coarse plaquette. The
  pattern rides on the first fine line link of the coarse link; no centrality is used.
* `sheet_emb`: of the four fine plaquettes of a block, the fine sheet meets only the first, and there it is the
  coarse sheet of the block. `fAct_moved_tw`: the moved twisted action in blocks.
* **`decimation_sheet`**: one `κ` serves both, for every `n`:
  `log Zmk C i (2n) = log Zh C (i+1) n + κ n⁴` and `log Zmktw C i P (2n) = log Ztw C (i+1) P n + κ n⁴`.
* **`vortexStep_eq`**: `vortexF C i P (2n) = vortexF C (i+1) P n + (holderExcessTw C i P (2n) − holderExcess C i (2n))`.
* **`vortex_antiDiagonal`**: `vortexF C 0 P (2^k s) = vortexF C k P s + Σ_{i<k} (E_i^tw − E_i)(2^{k−i} s)`, and
  `vortex_antiDiagonal_crossing`: `vortexF C 0 P (2^{k+2}) = vortexF C k P 4 + Σ_{i<k} (E_i^tw − E_i)(2^{k+2−i})`.
* `twistRatioN_eq_vortex`, `one_sub_twistRatioN_le_vortexF`: on the chain from `2β`, the step-`0` single-twist
  ratio of the Wilson torus is `exp(−vortexF C 0 (0, ν) n)`; the chain's constant shift cancels.
* `fluxShareN_zero_le_of_vortex`: `vortexF C 0 (0, ν) (2^{k+2}) ≤ η` for the three `ν` gives step-`0` flux share
  `≤ 9η` (`TwistDeficitUnionN.fluxShareN_le_of_single` at `N = 2`).
* `sectorSeed_of_vortex`: `VortexStepNet ε`, `VortexChainEnd δ` with `9(ε + δ) ≤ 1/80000`, and `SectorRest`
  give `GapSideTwistFlat.FirstCrossingSectorSeed`.

## What is open

* `VortexStepNet ε`: the sign and size of `Σ_{i<k} (E_i^tw − E_i)` at the first crossing. Each term is the
  difference of two Hölder excesses with the same extensive density; nothing here bounds it.
* `VortexChainEnd δ`: the chain end `vortexF C k P 4`. The class-weight converse of
  `CentreSectorSeedN.sectors_of_defectWN` is not built. Budget: `ε + δ ≤ 1/720000`.
* `SectorRest`: the flux shares of corner steps `1–3` and every zero-flux defect. The anti-diagonal lives on
  cubic tori (`HolderBondMoving`), which carry step `0` only; steps `1–3` are rectangular tori.
* The sign `0 ≤ holderExcessTw` at even sides is `GapSideVortexStepSign.holderExcessTw_nonneg` (a gauge-shifted
  move along the in-plane directions). It is the lower side of the step; `VortexStepNet` needs the upper side.

## Controls

`decimation_twist` and `conv_centre_shift` hold for every compact group, `U(1)` included: they are identities
and carry no sign. The chain and the Weyl constant enter only `κ`, which cancels in `vortexStep_eq`. For
`U(1)` the twisted action is positive at every configuration (`GapSideTwistFlat.twistedAction_pos_of_comm`),
so (argued, not built here) the Coulomb twist cost stays at least of order `2β` at every side while the `U(1)`
chain crosses, and the `U(1)` form of `VortexStepNet` is false at small `ε`. Nothing here moves `U(1)` toward
confinement.

DERIVED (module-wide): `64`, `8`, `6`, `4 n⁴` and `π` as in `ElectricExactProof`; `0` the sheet coordinate
(`GapSideTwistFlat.sheet`); `2^{k+2}` and `4 = 2²` the crossing side and its image; `9 = 9 ⌊2/2⌋²` the
single-twist union bound of `TwistDeficitUnionN` at `N = 2`; `720000 = 9 · 80000`.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace MassGap.GapSideVortexAntiDiagonal

open MeasureTheory Set Real Filter MassGap.CompactGauge MassGap.SUN MassGap.TorusDoubling
  MassGap.HolderBondMoving MassGap.ConvolutionTransfer MassGap.ChainCoarseSeed
  MassGap.ChainFirstCrossing MassGap.ElectricStep MassGap.ElectricStepChain
  MassGap.SU2DiskLaw MassGap.MovedTorusDecimation MassGap.ElectricExactProof
open MassGap.TwistedTraceBound (negOne coe_negOne)

/-! ## 1. Convolution and a translation -/

section Centre

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [Nonempty G] [MeasurableSpace G] [BorelSpace G]

/-- **A translation commutes with the convolution**: `(u(z ·) ⋆ v)(g) = (u ⋆ v)(z g)`, for every `z`. -/
theorem conv_centre_shift (u v : G → ℝ) (z g : G) :
    conv (fun x => u (z * x)) v g = conv u v (z * g) := by
  unfold conv
  rw [← integral_mul_left_eq_self (μ := probHaar G) (fun h => u h * v (h⁻¹ * (z * g))) z]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only
  rw [show (z * h)⁻¹ * (z * g) = h⁻¹ * g by group]

/-- **The fourfold convolution with one translated factor** is the fourfold convolution translated:
`((w(z ·) ⋆ w) ⋆ (w ⋆ w))(g) = ((w ⋆ w) ⋆ (w ⋆ w))(z g)`. -/
theorem K4_centre_shift (w : G → ℝ) (z g : G) :
    conv (conv (fun x => w (z * x)) w) (conv w w) g = conv (conv w w) (conv w w) (z * g) := by
  have e : conv (fun x => w (z * x)) w = fun x => conv w w (z * x) :=
    funext fun x => conv_centre_shift w w z x
  rw [e, conv_centre_shift]

end Centre

/-! ## 2. The twisted block and its decimation, for any compact group -/

section Block

variable {n : ℕ}
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [Nonempty G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

/-- **The four fine plaquettes of the block `(X, p)`, with `τ_{X,p}` multiplied into the first.** -/
def blockWtw (w : G → ℝ) (τ : TSite 4 n → Plane → G) (U : TLink 4 (2 * n) → G) (X : TSite 4 n)
    (p : Plane) : ℝ :=
  w (τ X p * thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 0 0)) U)
    * w (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 1 0)) U)
    * w (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 0 1)) U)
    * w (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 1 1)) U)

/-- The twisted block weight of the assembled configuration, in the three parts. -/
theorem blockWtw_asm (w : G → ℝ) (τ : TSite 4 n → Plane → G) (c : Cfg n G) (X : TSite 4 n)
    (p : Plane) :
    blockWtw w τ (asm c) X p =
      w (τ X p * ((c.1.1 (p.1.1, X)).1 * (c.1.2 (X, p)).2.1 * ((c.1.2 (X, p)).1.1)⁻¹
          * ((c.1.1 (p.1.2, X)).1)⁻¹))
      * w ((c.1.1 (p.1.1, X)).2 * (c.1.1 (p.1.2, tshift p.1.1 X)).1 * ((c.1.2 (X, p)).1.2)⁻¹
          * ((c.1.2 (X, p)).2.1)⁻¹)
      * w ((c.1.2 (X, p)).1.1 * (c.1.2 (X, p)).2.2 * ((c.1.1 (p.1.1, tshift p.1.2 X)).1)⁻¹
          * ((c.1.1 (p.1.2, X)).2)⁻¹)
      * w ((c.1.2 (X, p)).1.2 * (c.1.1 (p.1.2, tshift p.1.1 X)).2 * ((c.1.1 (p.1.1, tshift p.1.2 X)).2)⁻¹
          * ((c.1.2 (X, p)).2.2)⁻¹) := by
  have hij := plane_ne p
  unfold blockWtw thol
  simp only
  rw [tshift_i_0, tshift_j_0 hij, tshift_i_1, tshift_j_0 hij, tshift_i_0, tshift_j_1 hij,
    tshift_i_1, tshift_j_1 hij]
  rw [lk_line_i p X 0, lk_line_j p X 0, lk_line_i p X 1, lk_line_j p (tshift p.1.1 X) 0,
    lk_line_j p X 1, lk_line_i p (tshift p.1.2 X) 0, lk_line_j p (tshift p.1.1 X) 1,
    lk_line_i p (tshift p.1.2 X) 1]
  rw [show ((p.1.2, emb X (par p.1.1 p.1.2 1 0)) : TLink 4 (2 * n)) = eZ (Sum.inr ((X, p), 2)) from rfl,
    show ((p.1.1, emb X (par p.1.1 p.1.2 0 1)) : TLink 4 (2 * n)) = eZ (Sum.inr ((X, p), 0)) from rfl,
    show ((p.1.1, emb X (par p.1.1 p.1.2 1 1)) : TLink 4 (2 * n)) = eZ (Sum.inr ((X, p), 1)) from rfl,
    show ((p.1.2, emb X (par p.1.1 p.1.2 1 1)) : TLink 4 (2 * n)) = eZ (Sum.inr ((X, p), 3)) from rfl]
  simp only [asm_line, asm_int]
  rfl

theorem continuous_blockWtw {w : G → ℝ} (hw : Continuous w) (τ : TSite 4 n → Plane → G)
    (X : TSite 4 n) (p : Plane) :
    Continuous fun U : TLink 4 (2 * n) → G => blockWtw w τ U X p := by
  unfold blockWtw
  exact (((hw.comp (continuous_const.mul (continuous_thol _))).mul (hw.comp (continuous_thol _))).mul
    (hw.comp (continuous_thol _))).mul (hw.comp (continuous_thol _))

/-- **The twisted moved-torus decimation, for any compact group.** A pattern `τ` multiplied into the first
fine plaquette of each block is, after the decimation, multiplied into the coarse plaquette. -/
theorem decimation_twist (w : G → ℝ) (hw : Continuous w) (hwc : ∀ k x, w (k * x * k⁻¹) = w x)
    (τ : TSite 4 n → Plane → G) :
    ∫ U, ∏ X : TSite 4 n, ∏ p : Plane, blockWtw w τ U X p
        ∂(Measure.pi fun _ : TLink 4 (2 * n) => probHaar G)
      = ∫ V, ∏ X : TSite 4 n, ∏ p : Plane,
          conv (conv w w) (conv w w) (τ X p * thol ((p.1.1, p.1.2), X) V)
          ∂(Measure.pi fun _ : TLink 4 n => probHaar G) := by
  set K4 := conv (conv w w) (conv w w) with hK4
  have hK4c : Continuous K4 := continuous_conv (continuous_conv hw hw) (continuous_conv hw hw)
  have hF : Continuous fun U : TLink 4 (2 * n) → G => ∏ X : TSite 4 n, ∏ p : Plane, blockWtw w τ U X p :=
    continuous_finsetProd _ fun X _ => continuous_finsetProd _ fun p _ => continuous_blockWtw hw τ X p
  rw [← (measurePreserving_asm (n := n) (G := G)).map_eq,
    integral_map measurable_asm.aemeasurable hF.aestronglyMeasurable]
  simp_rw [blockWtw_asm]
  set Bk : (TLink 4 n → G × G) → TSite 4 n → Plane → (G × G) × (G × G) → ℝ := fun A X p q =>
    w (τ X p * ((A (p.1.1, X)).1 * q.2.1 * q.1.1⁻¹ * ((A (p.1.2, X)).1)⁻¹))
      * w ((A (p.1.1, X)).2 * (A (p.1.2, tshift p.1.1 X)).1 * q.1.2⁻¹ * q.2.1⁻¹)
      * w (q.1.1 * q.2.2 * ((A (p.1.1, tshift p.1.2 X)).1)⁻¹ * ((A (p.1.2, X)).2)⁻¹)
      * w (q.1.2 * (A (p.1.2, tshift p.1.1 X)).2 * ((A (p.1.1, tshift p.1.2 X)).2)⁻¹ * q.2.2⁻¹)
    with hBk
  set H : (TLink 4 n → G × G) × (TSite 4 n × Plane → (G × G) × (G × G)) → ℝ :=
    fun ab => ∏ X : TSite 4 n, ∏ p : Plane, Bk ab.1 X p (ab.2 (X, p)) with hH
  have hHc : Continuous H := by
    refine continuous_finsetProd _ fun X _ => continuous_finsetProd _ fun p _ => ?_
    simp only [hBk]
    fun_prop
  rw [show (fun c : Cfg n G => ∏ X : TSite 4 n, ∏ p : Plane, Bk c.1.1 X p (c.1.2 (X, p)))
      = fun c => H c.1 from rfl, integral_fun_fst H, probReal_univ, one_smul,
    integral_prod H (integrable_of_continuous hHc)]
  have hB : ∀ A : TLink 4 n → G × G,
      ∫ B, H (A, B) ∂(Measure.pi fun _ : TSite 4 n × Plane =>
        ((probHaar G).prod (probHaar G)).prod ((probHaar G).prod (probHaar G)))
      = ∏ X : TSite 4 n, ∏ p : Plane,
          K4 (τ X p * thol ((p.1.1, p.1.2), X) fun l => (A l).1 * (A l).2) := by
    intro A
    have e : (fun B : TSite 4 n × Plane → (G × G) × (G × G) => H (A, B))
        = fun B => ∏ xp : TSite 4 n × Plane, Bk A xp.1 xp.2 (B xp) := by
      funext B
      simp only [hH]
      rw [Fintype.prod_prod_type]
    rw [e, integral_fintype_prod_eq_prod (fun (xp : TSite 4 n × Plane) q => Bk A xp.1 xp.2 q),
      Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun X _ => Finset.prod_congr rfl fun p _ => ?_
    simp only [hBk]
    have e2 : ∀ q : (G × G) × (G × G),
        τ X p * ((A (p.1.1, X)).1 * q.2.1 * q.1.1⁻¹ * ((A (p.1.2, X)).1)⁻¹)
          = τ X p * (A (p.1.1, X)).1 * q.2.1 * q.1.1⁻¹ * ((A (p.1.2, X)).1)⁻¹ := fun q => by group
    simp_rw [e2]
    rw [block_integral w hw hwc]
    congr 1
    simp only [thol]
    group
  simp_rw [hB]
  exact integral_shear (fun V => ∏ X : TSite 4 n, ∏ p : Plane, K4 (τ X p * thol ((p.1.1, p.1.2), X) V))
    (continuous_finsetProd _ fun X _ => continuous_finsetProd _ fun p _ =>
      hK4c.comp (continuous_const.mul (continuous_thol _)))

end Block

/-! ## 3. The sheet on the fine and the coarse torus -/

section Sheet

/-- The coarse sheet on the plaquette `(p, X)`: `−1` when `p = P` and `X_a = X_b = 0`. -/
def tauC {n : ℕ} (P : Plane) (X : TSite 4 n) (p : Plane) : SU 2 :=
  GapSideTwistFlat.sheet P.1.1 P.1.2 negOne (((p.1.1, p.1.2), X) : TPlaq 4 n)

theorem sheet_diag {d N : ℕ} {a b : Fin d} (hab : a ≠ b) (z : SU 2) (k : Fin d) (x : TSite d N) :
    GapSideTwistFlat.sheet a b z (((k, k), x) : TPlaq d N) = 1 := by
  unfold GapSideTwistFlat.sheet
  rw [if_neg]
  rintro ⟨h | h, -⟩
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact hab (h1.symm.trans h2)
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact hab (h2.symm.trans h1)

theorem sheet_swap {d N : ℕ} (a b : Fin d) (z : SU 2) (i j : Fin d) (x : TSite d N) :
    GapSideTwistFlat.sheet a b z (((j, i), x) : TPlaq d N)
      = GapSideTwistFlat.sheet a b z (((i, j), x) : TPlaq d N) := by
  unfold GapSideTwistFlat.sheet
  exact if_congr (by simp only [Prod.mk.injEq]; tauto) rfl rfl

theorem sheet_val {d N : ℕ} (a b : Fin d) (q : TPlaq d N) :
    GapSideTwistFlat.sheet a b negOne q = negOne ∨ GapSideTwistFlat.sheet a b negOne q = 1 := by
  unfold GapSideTwistFlat.sheet
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `½ Re tr` does not see the orientation of a sheet plaquette: `−1` is central and its own inverse. -/
theorem suTau_sheet_inv (s : SU 2) (hs : s = negOne ∨ s = 1) (g : SU 2) :
    suTau (s * g⁻¹) = suTau (s * g) := by
  rw [← suTau_inv (s * g⁻¹), mul_inv_rev, inv_inv]
  rcases hs with rfl | rfl
  · rw [GapSideTwistFlat.negOne_inv]
    congr 1
    exact (Subtype.ext (by simp [coe_negOne]) : negOne * g = g * negOne).symm
  · simp

theorem halfField_sheet_sym {d N : ℕ} (W : ℝ → ℝ) (a b : Fin d) (i j : Fin d) (x : TSite d N)
    (g : SU 2) :
    halfField W suTau (GapSideTwistFlat.sheet a b negOne (((j, i), x) : TPlaq d N) * g⁻¹)
      = halfField W suTau (GapSideTwistFlat.sheet a b negOne (((i, j), x) : TPlaq d N) * g) := by
  rw [sheet_swap]
  unfold halfField chainField
  rw [suTau_sheet_inv _ (sheet_val a b _)]

variable {n : ℕ}

theorem emb_val (X : TSite 4 n) (ε : Fin 4 → Fin 2) (k : Fin 4) :
    (emb X ε k).val = 2 * (X k).val + (ε k).val := rfl

/-- **The fine sheet meets a block in its first plaquette only**, and there it is the coarse sheet. -/
theorem sheet_emb (P p : Plane) (X : TSite 4 n) (a b : Fin 2) :
    GapSideTwistFlat.sheet P.1.1 P.1.2 negOne
        (((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 a b)) : TPlaq 4 (2 * n))
      = if a = 0 ∧ b = 0 then tauC P X p else 1 := by
  have hp := p.2
  have hP := P.2
  unfold tauC GapSideTwistFlat.sheet
  simp only [emb_val]
  by_cases h1 : p.1.1 = P.1.1 ∧ p.1.2 = P.1.2
  · obtain ⟨e1, e2⟩ := h1
    have hne : p.1.1 ≠ p.1.2 := hp.ne
    rw [← e1, ← e2]
    simp only [par_i, par_j hne, true_or, true_and]
    fin_cases a <;> fin_cases b <;> simp
  · have c1 : ¬ ((p.1.1, p.1.2) = (P.1.1, P.1.2)) := fun h => h1 (Prod.mk.inj h)
    have c2 : ¬ ((p.1.1, p.1.2) = (P.1.2, P.1.1)) := fun h => by
      obtain ⟨e1, e2⟩ := Prod.mk.inj h
      rw [e1, e2] at hp
      exact lt_asymm hp hP
    simp only [c1, c2, false_or, false_and, if_false, ite_self]

end Sheet

/-! ## 4. The moved twisted action, block by block -/

section Action

variable {N : ℕ}

theorem mkField_eq (Φ : TPlaq 4 N → SU 2 → ℝ) (q : TPlaq 4 N) (g : SU 2) :
    mkField Φ q g
      = if Survives q then 2 ^ (Finset.univ.filter fun κ : Fin 4 => ¬ inK κ q).card * Φ q g else 0 := by
  unfold mkField
  rw [moveIter_eq _ _ 4 le_rfl]
  simp only [Finset.mem_univ, true_implies, Fin.is_lt, true_and]
  rfl

variable {n : ℕ}

/-- **The moved twisted action in blocks.** For an inverse-invariant density `h` and a twist pattern `ζ`
trivial on the diagonal and blind to orientation under `h`,
`fAct (mkField (1 · h(ζ ·))) U = 64 n⁴ h(1) + Σ_X Σ_p 8 Σ_{a,b} h(ζ · hol)` at the plaquettes `2X + a eᵢ + b eⱼ`. -/
theorem fAct_moved_tw (h : SU 2 → ℝ) (ζ : TPlaq 4 (2 * n) → SU 2)
    (hdiag : ∀ i x, ζ ((i, i), x) = 1)
    (hsym : ∀ i j x g, h (ζ ((j, i), x) * g⁻¹) = h (ζ ((i, j), x) * g))
    (U : TLink 4 (2 * n) → SU 2) :
    fAct (mkField (twistField 1 h ζ)) U
      = (64 * (n : ℝ) ^ 4) * h 1 + ∑ X : TSite 4 n, ∑ p : Plane, 8 * ∑ a : Fin 2, ∑ b : Fin 2,
          h (ζ ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 a b))
            * thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 a b)) U) := by
  set Φ := mkField (twistField 1 h ζ) with hΦ
  unfold fAct
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hx : ∀ x : TSite 4 (2 * n), ∑ q : Fin 4 × Fin 4, Φ (q, x) (thol (q, x) U)
      = ∑ i : Fin 4, Φ ((i, i), x) 1
        + 2 * ∑ q ∈ Finset.univ.filter (fun q : Fin 4 × Fin 4 => q.1 < q.2), Φ (q, x) (thol (q, x) U) := by
    intro x
    rw [sum_pairs_of_symm (fun q => Φ (q, x) (thol (q, x) U)) (fun i j => by
      show Φ ((j, i), x) (thol ((j, i), x) U) = Φ ((i, j), x) (thol ((i, j), x) U)
      rw [hΦ, mkField_eq, mkField_eq, thol_swap]
      simp only [twistField, one_mul]
      rw [hsym]
      simp only [Survives, inK, evenAt, or_comm])]
    simp only [thol_diag]
  rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_add_distrib]
  congr 1
  · -- the diagonal pairs
    rw [sum_fine]
    have e : ∀ (X : TSite 4 n) (ε : Fin 4 → Fin 2), ∑ i : Fin 4, Φ ((i, i), emb X ε) 1
        = ∑ i : Fin 4, if (∀ κ, ¬ (i = κ ∨ i = κ) → ε κ = 0) then 8 * h 1 else 0 := by
      intro X ε
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hΦ, mkField_eq, card_diag]
      simp only [survives_emb, twistField, hdiag, one_mul, mul_one]
      norm_num
    simp_rw [e]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 4 → Fin 2))) (t := Finset.univ),
      ← Finset.sum_filter, Finset.sum_const, card_survive_diag]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_fun, nsmul_eq_mul]
    push_cast
    ring
  · -- the pairs `i < j`
    have e1 : ∀ x : TSite 4 (2 * n),
        2 * ∑ q ∈ Finset.univ.filter (fun q : Fin 4 × Fin 4 => q.1 < q.2), Φ (q, x) (thol (q, x) U)
        = ∑ p : Plane, 2 * Φ (p.1, x) (thol (p.1, x) U) := by
      intro x
      rw [Finset.mul_sum]
      exact Finset.sum_subtype _ (by simp) (fun q => 2 * Φ (q, x) (thol (q, x) U))
    simp_rw [e1]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun (p : Plane) _ =>
      sum_fine (fun x => 2 * Φ (p.1, x) (thol (p.1, x) U))]
    have e2 : ∀ (p : Plane) (X : TSite 4 n), ∑ ε : Fin 4 → Fin 2,
        2 * Φ (p.1, emb X ε) (thol (p.1, emb X ε) U)
        = 8 * ∑ a : Fin 2, ∑ b : Fin 2, h (ζ ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 a b))
            * thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 a b)) U) := by
      intro p X
      have hne := plane_ne p
      have e3 : ∀ ε : Fin 4 → Fin 2, 2 * Φ (p.1, emb X ε) (thol (p.1, emb X ε) U)
          = if ∀ κ, ¬ (p.1.1 = κ ∨ p.1.2 = κ) → ε κ = 0
            then 8 * h (ζ ((p.1.1, p.1.2), emb X ε) * thol ((p.1.1, p.1.2), emb X ε) U) else 0 := by
        intro ε
        rw [hΦ, mkField_offDiag _ hne]
        simp only [twistField, one_mul]
        rw [show (p.1, emb X ε) = ((p.1.1, p.1.2), emb X ε) from rfl]
        simp only [survives_emb]
        split_ifs
        · norm_num; ring
        · norm_num
      simp_rw [e3]
      rw [sum_survive hne, Finset.mul_sum]
      simp_rw [Finset.mul_sum]
    simp_rw [e2]
    rw [Finset.sum_comm]

/-- **The twisted action of the chain field on the coarse torus**: a constant plus the twisted chain field
over the plaquettes `i < j`. -/
theorem fAct_tw_coarse (W : ℝ → ℝ) (ζ : TPlaq 4 n → SU 2) (hdiag : ∀ i x, ζ ((i, i), x) = 1)
    (hsym : ∀ i j x g, halfField W suTau (ζ ((j, i), x) * g⁻¹) = halfField W suTau (ζ ((i, j), x) * g))
    (U : TLink 4 n → SU 2) :
    fAct (twistField 1 (halfField W suTau) ζ) U
      = (4 * n ^ 4 : ℕ) * halfField W suTau 1 + ∑ x : TSite 4 n,
          ∑ p ∈ Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2),
            chainField W suTau (ζ (p, x) * thol (p, x) U) := by
  unfold fAct twistField
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hx : ∀ x : TSite 4 n, ∑ p : Fin 4 × Fin 4, 1 * halfField W suTau (ζ (p, x) * thol (p, x) U)
      = 4 * halfField W suTau 1 + ∑ p ∈ Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2),
          chainField W suTau (ζ (p, x) * thol (p, x) U) := by
    intro x
    rw [sum_pairs_of_symm (fun p => 1 * halfField W suTau (ζ (p, x) * thol (p, x) U)) (fun i j => by
      show 1 * halfField W suTau (ζ ((j, i), x) * thol ((j, i), x) U)
        = 1 * halfField W suTau (ζ ((i, j), x) * thol ((i, j), x) U)
      rw [thol_swap, hsym])]
    simp only [thol_diag, hdiag, mul_one, one_mul, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold halfField
    ring
  rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
  simp only [TSite, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end Action

/-! ## 5. The twisted partition functions and the decimation with the same constant -/

section Partition

variable {β : ℝ} (C : WilsonChain β)

/-- The side-`n` torus at weight `W_i`, twisted by the sheet in the plane `P`. -/
def Ztw (i : ℕ) (P : Plane) (n : ℕ) : ℝ :=
  ZF (d := 4) (N := n) (probHaar (SU 2))
    (twistField 1 (halfField (C.W i) suTau) (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne))

/-- The moved twisted torus: the bond moves of every direction applied to the twisted field. -/
def Zmktw (i : ℕ) (P : Plane) (n : ℕ) : ℝ :=
  ZF (d := 4) (N := n) (probHaar (SU 2))
    (mkField (twistField 1 (halfField (C.W i) suTau) (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne)))

/-- **The twisted Hölder excess** at side `m`, the twin of `ElectricStepChain.holderExcess`. -/
def holderExcessTw (i : ℕ) (P : Plane) (m : ℕ) : ℝ :=
  Real.log (Zmktw C i P m) - Real.log (Ztw C i P m)

/-- **The vortex free energy** of the chain torus: `−log(Z_tw/Z)` at weight `W_i`, side `n`, sheet in `P`. -/
def vortexF (i : ℕ) (P : Plane) (n : ℕ) : ℝ :=
  -Real.log (Ztw C i P n / Zh C i n)

/-- The coarse integral with the coarse sheet. -/
def Jtw (i : ℕ) (P : Plane) (n : ℕ) : ℝ :=
  ∫ V, ∏ X : TSite 4 n, ∏ p : Plane, K4 C i (tauC P X p * thol ((p.1.1, p.1.2), X) V)
    ∂(Measure.pi fun _ : TLink 4 n => probHaar (SU 2))

theorem Jtw_pos (i : ℕ) (P : Plane) (n : ℕ) : 0 < Jtw C i P n := by
  unfold Jtw
  have hc : Continuous fun V : TLink 4 n → SU 2 =>
      ∏ X : TSite 4 n, ∏ p : Plane, K4 C i (tauC P X p * thol ((p.1.1, p.1.2), X) V) :=
    continuous_finsetProd _ fun X _ => continuous_finsetProd _ fun p _ =>
      (continuous_K4 C i).comp (continuous_const.mul (continuous_thol _))
  have hpos : ∀ V : TLink 4 n → SU 2,
      0 < ∏ X : TSite 4 n, ∏ p : Plane, K4 C i (tauC P X p * thol ((p.1.1, p.1.2), X) V) :=
    fun V => Finset.prod_pos fun X _ => Finset.prod_pos fun p _ => K4_pos C i _
  rw [integral_pos_iff_support_of_nonneg (fun V => (hpos V).le) (integrable_of_continuous hc)]
  rw [show Function.support (fun V : TLink 4 n → SU 2 =>
      ∏ X : TSite 4 n, ∏ p : Plane, K4 C i (tauC P X p * thol ((p.1.1, p.1.2), X) V)) = univ from
    Set.eq_univ_of_forall fun V => (hpos V).ne', measure_univ]
  exact one_pos

theorem continuous_halfField (k : ℕ) : Continuous (halfField (C.W k) suTau) := by
  unfold halfField chainField
  exact (((continuous_W C k).comp continuous_suTau).log
    fun g => (W_pos C k _ (suTau_mem g)).ne').neg.div_const 2

/-- A partition function of continuous plaquette densities is positive. -/
theorem ZF_pos {n : ℕ} (Φ : TPlaq 4 n → SU 2 → ℝ) (hΦ : ∀ q, Continuous (Φ q)) :
    0 < ZF (probHaar (SU 2)) Φ := by
  unfold ZF
  have hc : Continuous fun U : TLink 4 n → SU 2 => Real.exp (-fAct Φ U) := by
    unfold fAct
    exact Real.continuous_exp.comp
      (continuous_finsetSum _ fun q _ => (hΦ q).comp (continuous_thol q)).neg
  rw [integral_pos_iff_support_of_nonneg (fun U => (Real.exp_pos _).le) (integrable_of_continuous hc)]
  rw [show Function.support (fun U : TLink 4 n → SU 2 => Real.exp (-fAct Φ U)) = univ from
    Set.eq_univ_of_forall fun U => (Real.exp_pos _).ne', measure_univ]
  exact one_pos

theorem Zh_pos (i n : ℕ) : 0 < Zh C i n :=
  ZF_pos _ fun _ => continuous_halfField C i

theorem Ztw_pos (i : ℕ) (P : Plane) (n : ℕ) : 0 < Ztw C i P n :=
  ZF_pos _ fun _ => continuous_const.mul ((continuous_halfField C i).comp
    (continuous_const.mul continuous_id))

/-- **The moved twisted side-`2n` torus** is the untwisted constant per coarse site times the twisted
coarse integral. -/
theorem Zmktw_eq (i : ℕ) (P : Plane) (n : ℕ) :
    Zmktw C i P (2 * n) = Real.exp (-(64 * (n : ℝ) ^ 4 * halfField (C.W i) suTau 1)) * Jtw C i P n := by
  unfold Zmktw ZF
  have hU : ∀ U : TLink 4 (2 * n) → SU 2,
      Real.exp (-fAct (mkField (twistField 1 (halfField (C.W i) suTau)
        (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne))) U)
      = Real.exp (-(64 * (n : ℝ) ^ 4 * halfField (C.W i) suTau 1))
        * ∏ X : TSite 4 n, ∏ p : Plane, blockWtw (wk C i) (tauC P) U X p := by
    intro U
    rw [fAct_moved_tw _ _ (fun k x => sheet_diag (ne_of_lt P.2) negOne k x)
      (fun a b x g => halfField_sheet_sym (C.W i) P.1.1 P.1.2 a b x g) U, neg_add, Real.exp_add,
      ← Finset.sum_neg_distrib, Real.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun X _ => ?_
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp only [Fin.sum_univ_two]
    rw [sheet_emb P p X 0 0, sheet_emb P p X 0 1, sheet_emb P p X 1 0, sheet_emb P p X 1 1]
    simp only [and_true, one_ne_zero, and_false, if_true, if_false, one_mul]
    set h := halfField (C.W i) suTau
    rw [show -(8 * (h (tauC P X p * thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 0 0)) U)
        + h (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 0 1)) U)
        + (h (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 1 0)) U)
        + h (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 1 1)) U))))
      = -(8 * h (tauC P X p * thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 0 0)) U))
        + -(8 * h (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 1 0)) U))
        + -(8 * h (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 0 1)) U))
        + -(8 * h (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 1 1)) U)) by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, exp_neg_eight_half, exp_neg_eight_half,
      exp_neg_eight_half, exp_neg_eight_half]
    rfl
  simp_rw [hU]
  rw [integral_const_mul]
  congr 1
  exact decimation_twist (wk C i) (continuous_wk C i) (wk_class C i) (tauC P)

/-- **The twisted side-`n` torus at `W_{i+1}`** is the untwisted constant per coarse site times the twisted
coarse integral. -/
theorem Ztw_succ_eq (i : ℕ) (P : Plane) (n : ℕ) :
    Ztw C (i + 1) P n = Real.exp (-(((4 * n ^ 4 : ℕ) : ℝ) * halfField (C.W (i + 1)) suTau 1))
      * cK C i ^ (6 * n ^ 4) * Jtw C i P n := by
  unfold Ztw ZF
  have hV : ∀ V : TLink 4 n → SU 2,
      Real.exp (-fAct (twistField 1 (halfField (C.W (i + 1)) suTau)
        (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne)) V)
      = Real.exp (-(((4 * n ^ 4 : ℕ) : ℝ) * halfField (C.W (i + 1)) suTau 1)) * cK C i ^ (6 * n ^ 4)
        * ∏ X : TSite 4 n, ∏ p : Plane, K4 C i (tauC P X p * thol ((p.1.1, p.1.2), X) V) := by
    intro V
    rw [fAct_tw_coarse _ _ (fun k x => sheet_diag (ne_of_lt P.2) negOne k x)
      (fun a b x g => halfField_sheet_sym (C.W (i + 1)) P.1.1 P.1.2 a b x g) V, neg_add, Real.exp_add,
      ← Finset.sum_neg_distrib, Real.exp_sum, mul_assoc]
    congr 1
    have e : ∀ X : TSite 4 n,
        Real.exp (-∑ q ∈ Finset.univ.filter (fun q : Fin 4 × Fin 4 => q.1 < q.2),
          chainField (C.W (i + 1)) suTau (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne (q, X) * thol (q, X) V))
        = cK C i ^ 6 * ∏ p : Plane, K4 C i (tauC P X p * thol ((p.1.1, p.1.2), X) V) := by
      intro X
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      have e1 : ∀ q : Fin 4 × Fin 4, Real.exp (-chainField (C.W (i + 1)) suTau
            (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne (q, X) * thol (q, X) V))
          = cK C i * K4 C i (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne (q, X) * thol (q, X) V) := by
        intro q
        unfold chainField
        rw [neg_neg, Real.exp_log (W_pos C (i + 1) _ (suTau_mem _)), W_succ_eq_K4]
        rfl
      simp_rw [e1]
      rw [Finset.prod_mul_distrib, Finset.prod_const, card_planes]
      congr 1
    simp_rw [e]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    simp only [TSite, Fintype.card_fun, Fintype.card_fin]
    rw [← pow_mul, mul_comm 6]
  simp_rw [hV]
  rw [integral_const_mul]
  rfl

/-- **The sheet survives the decimation with the same constant.** One `κ` (the constant of
`ElectricExactProof.electricExact`) gives, at every side `n`, both the untwisted and the sheet-twisted
moved-torus decimation. -/
theorem decimation_sheet (i : ℕ) (P : Plane) : ∃ κ : ℝ, ∀ n : ℕ,
    Real.log (Zmk C i (2 * n)) = Real.log (Zh C (i + 1) n) + κ * (n : ℝ) ^ 4 ∧
    Real.log (Zmktw C i P (2 * n)) = Real.log (Ztw C (i + 1) P n) + κ * (n : ℝ) ^ 4 := by
  refine ⟨-64 * halfField (C.W i) suTau 1 + 4 * halfField (C.W (i + 1)) suTau 1
    - 6 * Real.log (cK C i), fun n => ⟨?_, ?_⟩⟩
  · have hJ := Jc_pos C i n
    have hK := cK_pos C i
    rw [Zmk_eq, Zh_eq, Real.log_mul (Real.exp_pos _).ne' hJ.ne', Real.log_exp,
      Real.log_mul (mul_pos (Real.exp_pos _) (pow_pos hK _)).ne' hJ.ne',
      Real.log_mul (Real.exp_pos _).ne' (pow_pos hK _).ne', Real.log_exp, Real.log_pow]
    push_cast
    ring
  · have hJ := Jtw_pos C i P n
    have hK := cK_pos C i
    rw [Zmktw_eq, Ztw_succ_eq, Real.log_mul (Real.exp_pos _).ne' hJ.ne', Real.log_exp,
      Real.log_mul (mul_pos (Real.exp_pos _) (pow_pos hK _)).ne' hJ.ne',
      Real.log_mul (Real.exp_pos _).ne' (pow_pos hK _).ne', Real.log_exp, Real.log_pow]
    push_cast
    ring

end Partition

/-! ## 6. The one-step identity and the anti-diagonal -/

section AntiDiagonal

variable {β : ℝ} (C : WilsonChain β) (P : Plane)

/-- **The vortex step**: `F(W_i, 2n) = F(W_{i+1}, n) + (E_i^tw − E_i)(2n)`. -/
theorem vortexStep_eq (i n : ℕ) :
    vortexF C i P (2 * n)
      = vortexF C (i + 1) P n + (holderExcessTw C i P (2 * n) - holderExcess C i (2 * n)) := by
  obtain ⟨κ, hκ⟩ := decimation_sheet C i P
  obtain ⟨h1, h2⟩ := hκ n
  unfold vortexF holderExcessTw holderExcess
  rw [Real.log_div (Ztw_pos C i P _).ne' (Zh_pos C i _).ne',
    Real.log_div (Ztw_pos C (i + 1) P _).ne' (Zh_pos C (i + 1) _).ne']
  linarith

/-- **The vortex anti-diagonal**, at every base side `s`. -/
theorem vortex_antiDiagonal (k s : ℕ) :
    vortexF C 0 P (2 ^ k * s) = vortexF C k P s + ∑ i ∈ Finset.range k,
      (holderExcessTw C i P (2 ^ (k - i) * s) - holderExcess C i (2 ^ (k - i) * s)) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [show 2 ^ (k + 1) * s = 2 ^ k * (2 * s) by ring, ih (2 * s), vortexStep_eq C P k s,
      Finset.sum_range_succ]
    have hs : ∀ i ∈ Finset.range k,
        holderExcessTw C i P (2 ^ (k - i) * (2 * s)) - holderExcess C i (2 ^ (k - i) * (2 * s))
          = holderExcessTw C i P (2 ^ (k + 1 - i) * s) - holderExcess C i (2 ^ (k + 1 - i) * s) := by
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      rw [show 2 ^ (k + 1 - i) * s = 2 ^ (k - i) * (2 * s) by
        rw [show k + 1 - i = (k - i) + 1 by omega, pow_succ]; ring]
    rw [Finset.sum_congr rfl hs, show k + 1 - k = 1 by omega, pow_one]
    ring

/-- **The vortex anti-diagonal at the first-crossing side**: the Wilson-side vortex free energy at side
`2^{k+2}` is the chain end at side `4` plus the summed vortex gaps of the steps. -/
theorem vortex_antiDiagonal_crossing (k : ℕ) :
    vortexF C 0 P (2 ^ (k + 2)) = vortexF C k P 4 + ∑ i ∈ Finset.range k,
      (holderExcessTw C i P (2 ^ (k + 2 - i)) - holderExcess C i (2 ^ (k + 2 - i))) := by
  have h := vortex_antiDiagonal C P k 4
  rw [show 2 ^ k * 4 = 2 ^ (k + 2) by ring] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i < k := Finset.mem_range.mp hi
  rw [show 2 ^ (k + 2 - i) = 2 ^ (k - i) * 4 by
    rw [show k + 2 - i = (k - i) + 2 by omega, pow_add]; norm_num]

end AntiDiagonal

/-! ## 7. The chain from `2β` at step `0` is the Wilson torus -/

section Wilson

local notation "wd" => WilsonAction.wilsonDensity

/-- The plane `(0, ν)`. -/
def plane0 (ν : {j : Fin 4 // j ≠ 0}) : Plane := ⟨((0 : Fin 4), ν.1), Fin.pos_iff_ne_zero.mpr ν.2⟩

/-- A constant added to every plaquette density multiplies `ZF` by `e^{−c · #plaquettes}`. -/
theorem ZF_add_const {n : ℕ} (Φ : TPlaq 4 n → SU 2 → ℝ) (c : ℝ) :
    ZF (probHaar (SU 2)) (fun q g => Φ q g + c)
      = Real.exp (-((Fintype.card (TPlaq 4 n) : ℝ) * c)) * ZF (probHaar (SU 2)) Φ := by
  unfold ZF fAct
  rw [← integral_const_mul]
  congr 1
  funext U
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Real.exp_add]
  congr 1
  ring

theorem halfField_zero_eq {β : ℝ} (C : WilsonChain (2 * β)) :
    halfField (C.W 0) suTau = fun g => β * wd g + (-β) := by
  funext g
  simp only [halfField, chainField, C.hW0, Real.log_exp, suTau]
  ring

/-- **The step-`0` single-twist ratio is the exponential of the chain's vortex free energy at step `0`.** -/
theorem twistRatioN_eq_vortex {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} [NeZero n] (hn : 2 ≤ n) (he : Even n)
    (C : WilsonChain (2 * β)) (ν : {j : Fin 4 // j ≠ 0}) :
    CentreSectorSeedN.twistRatioN 2 β n 0 (Pi.single ν 1) = Ztw C 0 (plane0 ν) n / Zh C 0 n := by
  rw [GapSideTwistBridge.twistRatioN_sheet hβ hn he ν]
  unfold Ztw Zh
  have e1 : twistField 1 (halfField (C.W 0) suTau)
      (GapSideTwistFlat.sheet (plane0 ν).1.1 (plane0 ν).1.2 negOne)
      = fun (q : TPlaq 4 n) g => twistField β wd (sheetTwist 0 ν.1 ((0, 0) : Fin n × Fin n) negOne) q g
        + (-β) := by
    funext q g
    rw [halfField_zero_eq C]
    simp only [twistField, plane0]
    rw [GapSideTwistBridge.sheet_eq_sheetTwist]
    ring
  have e2 : uniformField (d := 4) (n := n) (halfField (C.W 0) suTau)
      = fun (q : TPlaq 4 n) g => (fun (_ : TPlaq 4 n) g => β * wd g) q g + (-β) := by
    funext q g
    rw [halfField_zero_eq C]
    rfl
  rw [e1, e2, ZF_add_const, ZF_add_const, mul_div_mul_left _ _ (Real.exp_pos _).ne']

/-- **The single-twist deficit is at most the vortex free energy.** -/
theorem one_sub_twistRatioN_le_vortexF {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (he : Even n) (C : WilsonChain (2 * β)) (ν : {j : Fin 4 // j ≠ 0}) :
    1 - CentreSectorSeedN.twistRatioN 2 β n 0 (Pi.single ν 1) ≤ vortexF C 0 (plane0 ν) n := by
  rw [twistRatioN_eq_vortex hβ hn he C ν]
  unfold vortexF
  have := Real.log_le_sub_one_of_pos (div_pos (Ztw_pos C 0 (plane0 ν) n) (Zh_pos C 0 n))
  linarith

/-- **Step-`0` flux share from the vortex free energies of the three sheets `(0, ν)`.**
DERIVED: `9 = 9 ⌊2/2⌋²`, `TwistDeficitUnionN.fluxShareN_le_of_single` at `N = 2`. -/
theorem fluxShareN_zero_le_of_vortex {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ ν : {j : Fin 4 // j ≠ 0},
      vortexF (WilsonChainExists.wilsonChainOf (2 * β)) 0 (plane0 ν) (2 ^ (k + 2)) ≤ η) :
    CentreSectorSeedN.fluxShareN 2 β (2 ^ (k + 2)) 0 ≤ 9 * η := by
  haveI : NeZero (2 ^ (k + 2)) := ⟨by positivity⟩
  have hn : 2 ≤ 2 ^ (k + 2) := DeltaLengthTower.two_le_two_pow (by omega : 1 ≤ k + 2)
  have he : Even (2 ^ (k + 2)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hs := TwistDeficitUnionN.fluxShareN_le_of_single (N := 2) hβ (2 ^ (k + 2)) 0 hη
    (fun ν => by
      have := one_sub_twistRatioN_le_vortexF hβ hn he (WilsonChainExists.wilsonChainOf (2 * β)) ν
      linarith [h ν])
  norm_num at hs
  linarith

end Wilson

/-! ## 8. The vortex net and the sector seed -/

section Net

open MassGap.WilsonChainExists

/-- **The vortex step net**: eventually in `β`, at the first crossing `k` of the chain from `2β`, for every
sheet plane the summed vortex gaps of the steps `i < k` along the anti-diagonal are at most `ε`.

DERIVED: `1/1000` the sharp seed of `DoublingSharp`, the first-crossing threshold; `2^{k+2}` the
crossing side and `2^{k+2−i}` its image at step `i`. -/
def VortexStepNet (ε : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ k : ℕ, coarseDefect (wilsonChainOf (2 * β)) k ≤ 1 / 1000 →
    (∀ i < k, 1 / 1000 < coarseDefect (wilsonChainOf (2 * β)) i) →
    ∀ P : Plane, ∑ i ∈ Finset.range k,
      (holderExcessTw (wilsonChainOf (2 * β)) i P (2 ^ (k + 2 - i))
        - holderExcess (wilsonChainOf (2 * β)) i (2 ^ (k + 2 - i))) ≤ ε

/-- **The chain end**: eventually in `β`, at the first crossing `k`, the vortex free energy of the chain torus
of side `4` at weight `W_k` is at most `δ` for every sheet plane.

DERIVED: `1/1000` the sharp seed of `DoublingSharp`, the first-crossing threshold; `4 = 2²` the image of
the crossing side `2^{k+2}` at step `k`. -/
def VortexChainEnd (δ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ k : ℕ, coarseDefect (wilsonChainOf (2 * β)) k ≤ 1 / 1000 →
    (∀ i < k, 1 / 1000 < coarseDefect (wilsonChainOf (2 * β)) i) →
    ∀ P : Plane, vortexF (wilsonChainOf (2 * β)) k P 4 ≤ δ

/-- **What the cubic anti-diagonal does not reach**: the flux shares of corner steps `1–3` (rectangular
tori) and the zero-flux defects of every step, at the first-crossing side.

DERIVED: `1/1000` the sharp seed of `DoublingSharp`; `1/80000` inherited from
`CentreSectorSeed.defectW_le_of_sectors`, where it is CHOSEN so that `15 · 5/80000 ≤ 1/1000`; `1–3` the
corner steps of the four directions; `2` the colour count and the doubling. -/
def SectorRest : Prop :=
  ∀ᶠ β in atTop, ∀ k : ℕ, coarseDefect (wilsonChainOf (2 * β)) k ≤ 1 / 1000 →
    (∀ i < k, 1 / 1000 < coarseDefect (wilsonChainOf (2 * β)) i) →
    (∀ i : Fin 4, i ≠ 0 → CentreSectorSeedN.fluxShareN 2 β (2 ^ (k + 2)) i ≤ 1 / 80000) ∧
      ∀ i : Fin 4, CentreSectorSeedN.trivialDefectN 2 β (2 ^ (k + 2)) i ≤ 1 / 80000

/-- **The sector seed from the vortex net**, given the chain end and the rest of the sectors. The step-`0`
flux half needs `9(ε + δ) ≤ 1/80000`, i.e. `ε + δ ≤ 1/720000`. -/
theorem sectorSeed_of_vortex {ε δ : ℝ} (hV : VortexStepNet ε) (hE : VortexChainEnd δ)
    (hb : 9 * (ε + δ) ≤ 1 / 80000) (hR : SectorRest) :
    GapSideTwistFlat.FirstCrossingSectorSeed := by
  unfold GapSideTwistFlat.FirstCrossingSectorSeed
  filter_upwards [hV, hE, hR, eventually_ge_atTop (0 : ℝ)] with β hV hE hR hβ
  intro k hk hmin i
  obtain ⟨hR1, hR2⟩ := hR k hk hmin
  refine ⟨?_, hR2 i⟩
  by_cases hi : i = 0
  · subst hi
    have hF : ∀ ν : {j : Fin 4 // j ≠ 0},
        vortexF (wilsonChainOf (2 * β)) 0 (plane0 ν) (2 ^ (k + 2)) ≤ max 0 (ε + δ) := by
      intro ν
      rw [vortex_antiDiagonal_crossing]
      have h1 := hV k hk hmin (plane0 ν)
      have h2 := hE k hk hmin (plane0 ν)
      exact le_max_of_le_right (by linarith)
    have hfl := fluxShareN_zero_le_of_vortex hβ k (le_max_left 0 (ε + δ)) hF
    have hm : 9 * max 0 (ε + δ) ≤ 1 / 80000 := by
      rcases le_total 0 (ε + δ) with h | h
      · rw [max_eq_right h]; exact hb
      · rw [max_eq_left h]; norm_num
    linarith
  · exact hR1 i hi

end Net

end MassGap.GapSideVortexAntiDiagonal

end

#print axioms MassGap.GapSideVortexAntiDiagonal.conv_centre_shift
#print axioms MassGap.GapSideVortexAntiDiagonal.K4_centre_shift
#print axioms MassGap.GapSideVortexAntiDiagonal.decimation_twist
#print axioms MassGap.GapSideVortexAntiDiagonal.sheet_emb
#print axioms MassGap.GapSideVortexAntiDiagonal.fAct_moved_tw
#print axioms MassGap.GapSideVortexAntiDiagonal.fAct_tw_coarse
#print axioms MassGap.GapSideVortexAntiDiagonal.Zmktw_eq
#print axioms MassGap.GapSideVortexAntiDiagonal.Ztw_succ_eq
#print axioms MassGap.GapSideVortexAntiDiagonal.decimation_sheet
#print axioms MassGap.GapSideVortexAntiDiagonal.vortexStep_eq
#print axioms MassGap.GapSideVortexAntiDiagonal.vortex_antiDiagonal
#print axioms MassGap.GapSideVortexAntiDiagonal.vortex_antiDiagonal_crossing
#print axioms MassGap.GapSideVortexAntiDiagonal.twistRatioN_eq_vortex
#print axioms MassGap.GapSideVortexAntiDiagonal.one_sub_twistRatioN_le_vortexF
#print axioms MassGap.GapSideVortexAntiDiagonal.fluxShareN_zero_le_of_vortex
#print axioms MassGap.GapSideVortexAntiDiagonal.sectorSeed_of_vortex
