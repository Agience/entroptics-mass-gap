import Mathlib
import MassGap.FluxDuality
import MassGap.TorusChain
import MassGap.GapSideTwistBridge

/-!
# MassGap.TwoSliceBridge — the Wilson torus state has the two-slice law `a²/A` at the cubic step

`FluxDuality.TwoSliceLaw ν β n i` says that under the state `ν` the spatial links of step `i` at times `0` and
`n/2` have joint density `a(x, y)² / A` against product Haar, with `a = halfKN N β n i = kT^{∗(n/2)}` and
`A = hs(a)`. This module proves it for the periodic Wilson state `PeriodicState.torusState hN (n − 1) β` (side
`n`, cubic) at step `i = 0`, every even `n ≥ 2` and every `β ≥ 0`. Declarations are in the namespace
`MassGap.TwoSliceBridge`.

## Proved

* **The observable.** `pairObs T t h = h ∘ (readSlice 0 T 0, readSlice 0 T t)` reads a continuous `h` on the
  spatial links of direction `0` at times `0` and `t`; `pairObs (Tr n 0) (n/2) h` is `h ∘ slicePair n 0`
  (`pairObs_slicePair`, by `rfl`). `winLocal_pairObs`: it reads only the time window `[0, t]`.
* **Index conventions.** The torus has side `M + 1 = n` in every direction (`TorusChain.Lc M`), so the slice
  extents `Tr n 0` are `Tc M` (`tr_zero_eq`). A spatial link at time `t` is `(ν, siteOf 0 t y)` with `ν ≠ 0`,
  read in chain variables as `V t (ν, y)`: `perpI_siteOf`, `readSlice_cfg`, and `winF_pairObs`
  (`winF (pairObs (Tc M) t h) V A = h (V 0, V t)`).
* **Identification with the torus state.** `TorusChain.torusState_winF` writes `torusState hN M β f` for a
  window observable as `Zc (winF f) / Zc 1`: the Wilson expectation of `RectWilson.sysR` at cubic extents
  (`TorusChain.expect_cubic`, `TorusIdentify.rbd_cubic`), sliced along `0` and closed by one transfer kernel.
* **The factorization with the two slices inserted** (`Zc_pair`). At `M = 2j + 1` (side `n = 2(j + 1)`):

      Zc (fun V _ => g (V 0, V (j+1))) = ∫∫ a(x, z)² g(x, z),   a = kT^{∗(j+1)}.

  The chain splits at time `j + 1` (`HiddenChain.chain_split`); integrating the axis links of each step gives
  `kT` (`TorusChain.kern_wt`); the second half closes to `a(V_{j+1}, x)` (`HiddenChain.chain_end_kern`), the first
  half to `a(x, z)` (`HiddenChain.chain_end_iter`), and `a` is symmetric (`CyclicKernel.iter_symm`). With `g = 1`
  this is `Zc 1 = hs(a)` (`Zc_one`).
* **`torusState_pairObs`**: `torusState hN (2j+1) β (pairObs (Tc (2j+1)) (j+1) h) = pairExp (hS 0 (Tc (2j+1)) N) a h`.
* **`twoSliceLaw_torusState`** (the bridge at step `0`): for `β ≥ 0`, even `n ≥ 2`,
  `TwoSliceLaw (torusState hN (n − 1) β) β n 0`.
* **The reads on the Wilson torus.** `fluxReadOf_torusState_iff`: `FluxReadOf (torusState hN (n−1) β) n 0 ε ↔
  fluxShareN N β n 0 ≤ ε`; `defectReadOf_torusState_iff`: the same for `DefectReadOf` and `trivialDefectN`. No
  bridge is assumed: both come from `twoSliceLaw_torusState`.
* **The strong-coupling witness on the Wilson torus.** `reads_strong_torus`: at `0 ≤ β ≤ 2^{-16}` and the
  side conditions of `SubstrateFluxRead.sectors_strong`, both step-`0` reads hold on `torusState hN (n − 1) β`.
  `eventually_reads_strong_torus`: at every large even side both hold at `1/80000`. The witness is the Wilson
  state itself, not `FluxDuality.capTorus`.

## Built downstream

* The steps `i = 1, 2, 3` are built in `RectTorusState`: `rectState` is the rectangular Wilson state,
  `twoSliceLaw_rectState` proves the bridge at every step, and `capturesReadTorus_capR` discharges
  `FluxDuality.CapturesReadTorus` for the Wilson family `capR`.

## Assumed

Nothing beyond the imported modules. `torusState hN (n − 1) β` is the finite-volume periodic state; the
measured-period tie `measPeriod (cap β n 0) = n` of `FluxDuality.SectorSeedRead` is proved downstream
(`RectTorusState.measPeriod_capR`, `N ≥ 2`, `n ≥ 1`).

DERIVED (module-wide): `0` the step and the first slice; `j + 1 = n/2` the second
slice and the half side, `2j + 2 = n` the side, `M + 1 = n` the extent; `2` the square in the density, the
least side and the halving; `1/80000`, `65536`, `4 + N⁶`, `N³/2` the constants of
`SubstrateFluxRead.sectors_strong` and `CentreSectorSeedN`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.TwoSliceBridge

open MeasureTheory Filter Topology
open MassGap.RectWilson MassGap.RectTransfer MassGap.HiddenChain MassGap.TorusChain
open MassGap.KernelPower (hs iter)
open MassGap.FluxDuality (readSlice siteOf siteOf_self siteOf_ne slicePair pairExp TwoSliceLaw FluxReadOf
  DefectReadOf fluxReadOf_iff defectReadOf_iff)
open MassGap.CentreSectorSeedN (hSN halfKN fluxShareN trivialDefectN)

variable {N : ℕ}

/-! ## 1. The two-slice observable and its window -/

/-- **The two-slice observable**: `h` read on the spatial links of direction `0` at times `0` and `t`.
DERIVED: `0` the step and the first slice. -/
def pairObs (T : {j : Fin 4 // j ≠ 0} → ℕ) (t : ℕ)
    (h : C((SpT 0 T → SUN.SU N) × (SpT 0 T → SUN.SU N), ℝ)) : C(GibbsSpec.IConf (SUN.SU N), ℝ) :=
  h.comp ((readSlice 0 T 0).prodMk (readSlice 0 T (t : ℤ)))

/-- `pairObs` at the half side is the observable of `FluxDuality.TwoSliceLaw`. DERIVED: `0`, `n/2`. -/
theorem pairObs_slicePair (n : ℕ) (h : C(FluxDuality.Slice N n 0 × FluxDuality.Slice N n 0, ℝ)) :
    pairObs (CentreSectorSeed.Tr n 0) (n / 2) h = h.comp (slicePair n 0) := rfl

/-- **The two-slice observable reads the window `[0, t]`.** DERIVED: `0`. -/
theorem winLocal_pairObs {T : {j : Fin 4 // j ≠ 0} → ℕ} (t : ℕ)
    (h : C((SpT 0 T → SUN.SU N) × (SpT 0 T → SUN.SU N), ℝ)) : WinLocal t (pairObs T t h) := by
  intro U U' hUU
  have e : ∀ s : ℤ, 0 ≤ s → s ≤ t → readSlice (N := N) 0 T s U = readSlice 0 T s U' := by
    intro s h0 h1
    funext l
    show U (l.1.1, siteOf 0 s l.2) = U' (l.1.1, siteOf 0 s l.2)
    exact hUU _ ⟨by show 0 ≤ siteOf 0 s l.2 0; rw [siteOf_self]; exact h0,
      by show siteOf 0 s l.2 0 ≤ (t : ℤ); rw [siteOf_self]; exact h1, fun hl => absurd hl l.1.2⟩
  show h (readSlice 0 T 0 U, readSlice 0 T (t : ℤ) U) = h (readSlice 0 T 0 U', readSlice 0 T (t : ℤ) U')
  rw [e 0 le_rfl (Int.natCast_nonneg t), e (t : ℤ) (Int.natCast_nonneg t) le_rfl]

/-! ## 2. Index conventions: slices of the cubic torus in chain variables -/

/-- **The slice extents of step `0` at side `M + 1` are the cubic ones.** DERIVED: `0`, `1`. -/
theorem tr_zero_eq {n M : ℕ} (h : n = M + 1) : CentreSectorSeed.Tr n 0 = Tc M := by
  funext k
  show DoublingWilson.ext n (CentreSectorSeed.pathV 0) k.1 = M + 1
  rw [GapSideTwistBridge.ext_pathV_zero, h]

/-- Reduction modulo the extent fixes a coordinate already inside it. DERIVED: `0`, `1`. -/
theorem finMod_natCast {M k : ℕ} (hk : k < M + 1) : InfiniteLattice.finMod M (k : ℤ) = ⟨k, hk⟩ := by
  apply Fin.ext
  show (((k : ℤ) % ((M : ℤ) + 1)).toNat) = k
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg k) (by omega), Int.toNat_natCast]

/-- The transverse site of a slice point, reduced, is the slice point. DERIVED: `0` the step. -/
theorem perpI_siteOf {M : ℕ} (t : ℤ) (y : TT 0 (Tc M)) : perpI M (siteOf 0 t y) = y := by
  funext k
  show InfiniteLattice.finMod M (siteOf 0 t y k.1) = y k
  rw [siteOf_ne]
  exact finMod_natCast (y k).2

/-- **A slice read on the chain configuration is the chain's slice.** DERIVED: `0` the step. -/
theorem readSlice_cfg {M : ℕ} (V : ℕ → Sl M N) (A : ℕ → Ax M N) {s : ℤ} (hs : 0 ≤ s) :
    readSlice 0 (Tc M) s (cfg M N V A) = V s.toNat := by
  funext l
  show cfg M N V A (l.1.1, siteOf 0 s l.2) = V s.toNat l
  rw [cfg_sp (l := (l.1.1, siteOf 0 s l.2)) l.1.2
    (by show 0 ≤ siteOf 0 s l.2 0; rw [siteOf_self]; exact hs)]
  show V (siteOf 0 s l.2 0).toNat (⟨l.1.1, l.1.2⟩, perpI M (siteOf 0 s l.2)) = V s.toNat l
  rw [siteOf_self, perpI_siteOf]

/-- **The two-slice observable in chain variables**: `winF (pairObs (Tc M) t h) V A = h (V 0, V t)`.
DERIVED: `0` the first slice. -/
theorem winF_pairObs {M t : ℕ} (h : C(Sl M N × Sl M N, ℝ)) (V : ℕ → Sl M N) (A : ℕ → Ax M N) :
    winF (pairObs (Tc M) t h) V A = h (V 0, V t) := by
  show h (readSlice 0 (Tc M) 0 (cfg M N V A), readSlice 0 (Tc M) (t : ℤ) (cfg M N V A)) = h (V 0, V t)
  rw [readSlice_cfg V A le_rfl, readSlice_cfg V A (Int.natCast_nonneg t), Int.toNat_natCast, Int.toNat_zero]

/-! ## 3. The factorization with the two slices inserted -/

/-- **The closed chain with the two slices inserted**: at `M = 2j + 1`,
`Zc (g (V 0, V (j+1))) = ∫∫ a(x, z)² g(x, z)` with `a = kT^{∗(j+1)}`. DERIVED: `2` the square; `j + 1` the half
side. -/
theorem Zc_pair (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (j : ℕ)
    (g : C(Sl (j + 1 + j) N × Sl (j + 1 + j) N, ℝ)) :
    Zc (j + 1 + j) N β (fun V _ => g (V 0, V (j + 1)))
      = ∫ x, ∫ z, iter (hS 0 (Tc (j + 1 + j)) N) (kT 0 (Tc (j + 1 + j)) N β) j x z ^ 2 * g (x, z)
          ∂hS 0 (Tc (j + 1 + j)) N ∂hS 0 (Tc (j + 1 + j)) N := by
  have hac : Continuous (Function.uncurry
      (iter (hS 0 (Tc (j + 1 + j)) N) (kT 0 (Tc (j + 1 + j)) N β) j)) :=
    SliceKernelPower.continuous_iter (μ := 0) (T := Tc (j + 1 + j)) (N := N) β j
  unfold Zc
  congr 1; funext x
  have step1 : chain (hS 0 (Tc (j + 1 + j)) N) (hA 0 (Tc (j + 1 + j)) N) (wt (j + 1 + j) N β) (j + 1 + j)
      (fun V _ => g (V 0, V (j + 1)) * kT 0 (Tc (j + 1 + j)) N β (V (j + 1 + j)) x) x
      = chain (hS 0 (Tc (j + 1 + j)) N) (hA 0 (Tc (j + 1 + j)) N) (wt (j + 1 + j) N β) (j + 1 + j)
      (fun V _ => g (V 0, V (j + 1))
        * kern (hA 0 (Tc (j + 1 + j)) N) (wt (j + 1 + j) N β) (sshift V (j + 1) j) x) x := by
    congr 1; funext V A
    rw [kern_wt]
    show _ = g (V 0, V (j + 1)) * kT 0 (Tc (j + 1 + j)) N β (V (j + (j + 1))) x
    rw [show j + (j + 1) = j + 1 + j by omega]
  have hsplit := chain_split (μ := hS 0 (Tc (j + 1 + j)) N) (ν := hA 0 (Tc (j + 1 + j)) N)
    (w := wt (j + 1 + j) N β) (j + 1) j
    (G1 := fun V (_ : ℕ → Ax (j + 1 + j) N) => g (V 0, V (j + 1)))
    (fun V (_ : ℕ → Ax (j + 1 + j) N) => kern (hA 0 (Tc (j + 1 + j)) N) (wt (j + 1 + j) N β) (V j) x) x
    (fun V V' A A' hV _ => by
      show g (V 0, V (j + 1)) = g (V' 0, V' (j + 1))
      rw [hV 0 (Nat.zero_le _), hV (j + 1) le_rfl])
  refine step1.trans (hsplit.trans ?_)
  have hend : ∀ z, chain (hS 0 (Tc (j + 1 + j)) N) (hA 0 (Tc (j + 1 + j)) N) (wt (j + 1 + j) N β) j
      (fun V (_ : ℕ → Ax (j + 1 + j) N) => kern (hA 0 (Tc (j + 1 + j)) N) (wt (j + 1 + j) N β) (V j) x) z
      = iter (hS 0 (Tc (j + 1 + j)) N) (kT 0 (Tc (j + 1 + j)) N β) j z x := by
    intro z; rw [chain_end_kern x j z, kern_wt]
  simp only [hend]
  set g' : Sl (j + 1 + j) N → ℝ := fun z =>
    g (x, z) * iter (hS 0 (Tc (j + 1 + j)) N) (kT 0 (Tc (j + 1 + j)) N β) j z x with hg'
  have hg'c : Continuous g' :=
    (g.continuous.comp (continuous_const.prodMk continuous_id)).mul
      (hac.comp (continuous_id.prodMk continuous_const))
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hg'c.continuousOn
  have hg'b : ∀ z, |g' z| ≤ B := fun z => by
    simpa [Real.norm_eq_abs] using hB z (Set.mem_univ z)
  have step3 : chain (hS 0 (Tc (j + 1 + j)) N) (hA 0 (Tc (j + 1 + j)) N) (wt (j + 1 + j) N β) (j + 1)
      (fun V _ => g (V 0, V (j + 1))
        * iter (hS 0 (Tc (j + 1 + j)) N) (kT 0 (Tc (j + 1 + j)) N β) j (V (j + 1)) x) x
      = chain (hS 0 (Tc (j + 1 + j)) N) (hA 0 (Tc (j + 1 + j)) N) (wt (j + 1 + j) N β) (j + 1)
      (fun V _ => g' (V (j + 1))) x :=
    chain_congr (j + 1) (fun V A hV => by rw [hg']; dsimp only; rw [hV])
  refine step3.trans ?_
  rw [chain_end_iter (μ := hS 0 (Tc (j + 1 + j)) N) (ν := hA 0 (Tc (j + 1 + j)) N)
    (wmeas_wt β) (abs_wt_le hN hβ) hg'c.measurable hg'b j x, kern_wt]
  congr 1; funext z
  rw [hg']
  dsimp only
  rw [CyclicKernel.iter_symm (μ := hS 0 (Tc (j + 1 + j)) N) (bdd_kT hN hβ) (kT_symm β) j z x]
  ring

/-- **The closed chain is the trace**: `Zc 1 = hs(a)`. DERIVED: no numeral. -/
theorem Zc_one (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (j : ℕ) :
    Zc (j + 1 + j) N β (fun _ _ => 1)
      = hs (hS 0 (Tc (j + 1 + j)) N) (iter (hS 0 (Tc (j + 1 + j)) N) (kT 0 (Tc (j + 1 + j)) N β) j) := by
  have e := Zc_pair hN hβ j (1 : C(Sl (j + 1 + j) N × Sl (j + 1 + j) N, ℝ))
  simp only [ContinuousMap.one_apply, mul_one] at e
  exact e

/-! ## 4. The two-slice law of the Wilson torus -/

/-- **The Wilson torus state on the two-slice observable**: at side `2j + 2`,
`torusState (pairObs h) = (∫∫ a² h) / hs(a)`. DERIVED: `j + 1` the half side. -/
theorem torusState_pairObs (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (j : ℕ)
    (h : C(Sl (j + 1 + j) N × Sl (j + 1 + j) N, ℝ)) :
    PeriodicState.torusState hN (j + 1 + j) β (pairObs (Tc (j + 1 + j)) (j + 1) h)
      = pairExp (hS 0 (Tc (j + 1 + j)) N)
          (iter (hS 0 (Tc (j + 1 + j)) N) (kT 0 (Tc (j + 1 + j)) N β) j) ⇑h := by
  rw [torusState_winF (M := j + 1 + j) hN hβ (winLocal_pairObs (j + 1) h) (by omega)]
  have e : winF (M := j + 1 + j) (pairObs (Tc (j + 1 + j)) (j + 1) h) = fun V _ => h (V 0, V (j + 1)) := by
    funext V A; exact winF_pairObs h V A
  rw [e, Zc_pair hN hβ j h, Zc_one hN hβ j]
  all_goals rfl

/-- The same at slice extents and a half side given up to equality. DERIVED: `1`. -/
theorem torusState_pairObs_of_eq (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (j : ℕ)
    {T : {k : Fin 4 // k ≠ 0} → ℕ} (hT : T = Tc (j + 1 + j)) {t : ℕ} (ht : t = j + 1)
    (h : C((SpT 0 T → SUN.SU N) × (SpT 0 T → SUN.SU N), ℝ)) :
    PeriodicState.torusState hN (j + 1 + j) β (pairObs T t h)
      = pairExp (hS 0 T N) (iter (hS 0 T N) (kT 0 T N β) (t - 1)) ⇑h := by
  subst hT ht
  rw [Nat.add_sub_cancel]
  exact torusState_pairObs hN hβ j h

/-- **The bridge at step `0`**: the periodic Wilson state of side `n` has the two-slice law `a²/A`.
DERIVED: `2` the least side; `0` the step; `1` in `n − 1`, the extent written as a successor. -/
theorem twoSliceLaw_torusState [NeZero N] (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n)
    (he : Even n) : TwoSliceLaw (PeriodicState.torusState hN (n - 1) β) β n 0 := by
  obtain ⟨j, hj⟩ : ∃ j, n = 2 * j + 2 := by
    obtain ⟨k, rfl⟩ := he
    exact ⟨k - 1, by omega⟩
  intro h
  have hM : n - 1 = j + 1 + j := by omega
  rw [hM]
  exact torusState_pairObs_of_eq hN hβ j (tr_zero_eq (by omega)) (t := n / 2) (by omega) h

/-! ## 5. The reads on the Wilson torus -/

/-- **The flux clause is the flux read of the Wilson torus.** DERIVED: `0` the step. -/
theorem fluxReadOf_torusState_iff [NeZero N] (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n)
    (he : Even n) {ε : ℝ} :
    FluxReadOf (PeriodicState.torusState hN (n - 1) β) n 0 ε ↔ fluxShareN N β n 0 ≤ ε :=
  fluxReadOf_iff hβ (twoSliceLaw_torusState hN hβ hn he)

/-- **The zero-flux clause is the zero-flux read of the Wilson torus.** DERIVED: `0` the step. -/
theorem defectReadOf_torusState_iff [NeZero N] (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n)
    (he : Even n) {ε : ℝ} :
    DefectReadOf (PeriodicState.torusState hN (n - 1) β) n 0 ε ↔ trivialDefectN N β n 0 ≤ ε :=
  defectReadOf_iff hβ (twoSliceLaw_torusState hN hβ hn he)

/-- **Both step-`0` reads hold on the Wilson torus at strong coupling.** DERIVED: `65536 = 2^{16}`;
`4 + N⁶`, `N³/2`, `2` from `sectors_strong` (`3` in `N^3 = |Z_N³|`, `6 = 2 · 3`). -/
theorem reads_strong_torus [NeZero N] (hN : N ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 65536) {n : ℕ}
    (hn : 2 ≤ n) (he : Even n)
    (hδ : (4 + (N : ℝ) ^ 6) * (β * StrongFiniteSize.strongBound n) ≤ 2) {ε : ℝ}
    (hεf : (N : ℝ) ^ 3 * (β * StrongFiniteSize.strongBound n) / 2 ≤ ε)
    (hεd : 2 * (β * StrongFiniteSize.strongBound n) ≤ ε) :
    FluxReadOf (PeriodicState.torusState hN (n - 1) β) n 0 ε ∧
      DefectReadOf (PeriodicState.torusState hN (n - 1) β) n 0 ε := by
  obtain ⟨hf, hd⟩ := SubstrateFluxRead.sectors_strong (N := N) hβ0 hβ hn he hδ 0
  exact ⟨(fluxReadOf_torusState_iff hN hβ0 hn he).mpr (hf.trans hεf),
    (defectReadOf_torusState_iff hN hβ0 hn he).mpr (hd.trans hεd)⟩

/-- **At strong coupling both step-`0` reads hold on the Wilson torus at `1/80000` at every large even side.**
DERIVED: `2` the least side; `1/80000` the threshold; `65536 = 2^{16}` the strong-coupling threshold. -/
theorem eventually_reads_strong_torus [NeZero N] (hN : N ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 65536) :
    ∀ᶠ n : ℕ in atTop, Even n →
      FluxReadOf (PeriodicState.torusState hN (n - 1) β) n 0 (1 / 80000) ∧
        DefectReadOf (PeriodicState.torusState hN (n - 1) β) n 0 (1 / 80000) := by
  have h1 := SubstrateFluxRead.eventually_sector_condition (N := N) β
  have h2 := (tendsto_order.mp (SubstrateFluxRead.tendsto_fluxBound (N := N) β)).2 (1 / 80000)
    (by norm_num)
  have h3 : ∀ᶠ n : ℕ in atTop, 2 * (β * StrongFiniteSize.strongBound n) < 1 / 80000 := by
    have h := (StrongFiniteSize.tendsto_strongBound.const_mul β).const_mul 2
    rw [mul_zero, mul_zero] at h
    exact (tendsto_order.mp h).2 _ (by norm_num)
  filter_upwards [h1, h2, h3, eventually_ge_atTop 2] with n hn1 hn2 hn3 hn4 he
  exact reads_strong_torus hN hβ0 hβ hn4 he hn1 hn2.le hn3.le

end MassGap.TwoSliceBridge

end

#print axioms MassGap.TwoSliceBridge.winLocal_pairObs
#print axioms MassGap.TwoSliceBridge.tr_zero_eq
#print axioms MassGap.TwoSliceBridge.readSlice_cfg
#print axioms MassGap.TwoSliceBridge.winF_pairObs
#print axioms MassGap.TwoSliceBridge.Zc_pair
#print axioms MassGap.TwoSliceBridge.Zc_one
#print axioms MassGap.TwoSliceBridge.torusState_pairObs
#print axioms MassGap.TwoSliceBridge.twoSliceLaw_torusState
#print axioms MassGap.TwoSliceBridge.fluxReadOf_torusState_iff
#print axioms MassGap.TwoSliceBridge.defectReadOf_torusState_iff
#print axioms MassGap.TwoSliceBridge.reads_strong_torus
#print axioms MassGap.TwoSliceBridge.eventually_reads_strong_torus
