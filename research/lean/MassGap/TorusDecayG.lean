import Mathlib
import MassGap.TorusDecay
import MassGap.TorusChainG
import MassGap.DoublingWilsonG
import MassGap.PeriodicReduceG

/-!
# MassGap.TorusDecayG — the finite-volume dyadic step for the Wilson model of `G`

`TorusDecay.dyadic_torus_decay` with `SUN.SU N` replaced by a `GaugeGroup G`.

`dyadic_torus_decayG`: at `β ≥ 0`, a power-of-two seed `n ≥ 2` with
`TorusDoubling.defectWG G 4 (wilsonDensityG G) β n ≤ 1/1000`, every gauge-invariant half-space
observable `x` and every `ε > 0`, eventually along `PeriodicReduceG.periodicUltraG G β`,

    torusConnG G 0 0 β j x n ≤ ½ · torusConnG G 0 0 β j x 0 + ε.

The proof is the `SU(N)` proof read on the objects of `TorusChainG`, `DoublingWilsonG` and
`PeriodicReduceG`: the torus of extent `2j + 2` in the ultrafilter is a dyadic corner `2ᵏ n`
(`periodicUltraG_seed_mem`); the doubling recursion gives the transfer gap on the vacuum complement
(`KernelGap.gap_of_excited`) and the excited weight `s ≤ (1/2)^{2ᵏ}` of the torus
(`DoublingSharp.excited_le_corner_sharp`); the torus state of the window observables is a ratio of
closed chains (`TorusChainG.torusStateG_winF`), and `ChainDecay.chain_decay` bounds the connected
pairing by the gap up to `100 B² √(2s)`.

DERIVED (module-wide): `4` the dimension; `0` the slicing direction and the reflection plane; `2` the
doubling, the even extent and the square; `1/2` the gap factor of `KernelGap.gap_of_excited`;
`1/1000` the sharp seed; `100`, `1/8` the constants of `ChainDecay.chain_decay`.
-/

namespace MassGap.TorusDecayG

open MeasureTheory Real Filter MassGap MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG
  MassGap.KernelPower MassGap.HiddenChain MassGap.ChainClosing MassGap.ChainReduce MassGap.ChainDecay
  MassGap.TorusChain MassGap.TorusChainG MassGap.DoublingRecursion MassGap.DoublingWilson
  MassGap.DoublingWilsonG MassGap.DoublingPower MassGap.SlabKernelOperator MassGap.PeriodicReduceG
  MassGap.GaugeGroup

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- The unit shift along `0`, iterated, is multiplicative. -/
theorem iterS_mulG (R : ℕ) (f g : C(GibbsSpec.IConf G, ℝ)) :
    (⇑(ReflectionShift.ishiftObsL (G := G) 0))^[R] (f * g)
      = (⇑(ReflectionShift.ishiftObsL (G := G) 0))^[R] f
        * (⇑(ReflectionShift.ishiftObsL (G := G) 0))^[R] g := by
  ext U
  rw [ContinuousMap.mul_apply, shiftObsG_iter, shiftObsG_iter, shiftObsG_iter,
    ContinuousMap.mul_apply]

theorem torusStateG_iterS (M : ℕ) (β : ℝ) (R : ℕ) (g : C(GibbsSpec.IConf G, ℝ)) :
    GaugeWilson.torusStateG G M β ((⇑(ReflectionShift.ishiftObsL (G := G) 0))^[R] g)
      = GaugeWilson.torusStateG G M β g := by
  induction R with
  | zero => rfl
  | succ R ih => rw [Function.iterate_succ_apply', ShiftInvG.torusStateG_shift, ih]

/-- The torus chain is the abstract closed chain. -/
theorem ZcG_eq {M : ℕ} {β : ℝ} (F : (ℕ → SlG G M) → (ℕ → AxG G M) → ℝ) :
    ZcG G M β F = Zh (hSG G 0 (Tc M)) (hAG G 0 (Tc M)) (wtG G M β) M F := by
  unfold ZcG Zh; rw [kern_wtG]

theorem torusStateG_Eh {M : ℕ} {β : ℝ} (hβ : 0 ≤ β) {w : ℕ}
    {g : C(GibbsSpec.IConf G, ℝ)} (hg : WinLocalG w g) (hw : w ≤ M) :
    GaugeWilson.torusStateG G M β g
      = Eh (hSG G 0 (Tc M)) (hAG G 0 (Tc M)) (wtG G M β) M (winFG g) := by
  rw [torusStateG_winF hβ hg hw, ZcG_eq, ZcG_eq]; rfl

/-- The step weight of the cubic torus as an abstract step. -/
theorem step_wtG {M : ℕ} {β : ℝ} (hβ : 0 ≤ β) : Step (wtG G M β) :=
  ⟨wmeas_wtG β, wtG_nonneg β, abs_wtG_le hβ⟩

theorem xWG_corner {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) {k j : ℕ}
    (hk : 2 * j + 2 = 2 ^ k * n) :
    xWG G n β (corner k) = Real.log (traceSeq (hSG G 0 (Tc (2 * j + 1)))
        (kern (hAG G 0 (Tc (2 * j + 1))) (wtG G (2 * j + 1) β)) (2 * (j + 1))) ∧
      xWG G n β (corner k + E 0) = Real.log (traceSeq (hSG G 0 (Tc (2 * j + 1)))
        (kern (hAG G 0 (Tc (2 * j + 1))) (wtG G (2 * j + 1) β)) (2 * (2 * (j + 1)))) := by
  have hL : ext n (corner k) = Lc (2 * j + 1) := by
    funext i; simp only [ext, corner, Lc]; omega
  have hT : tr (ext n (corner k)) 0 = Tc (2 * j + 1) := by rw [hL]
  have hT2 : tr (ext n (corner k + E 0)) 0 = Tc (2 * j + 1) := by rw [tr_ext_add, hT]
  have h0 : ext n (corner k) 0 = 2 * (j + 1) := by rw [hL]; simp only [Lc]; omega
  have h20 : ext n (corner k + E 0) 0 = 2 * (2 * (j + 1)) := by rw [ext_add_self, h0]
  rw [kern_wtG]
  refine ⟨?_, ?_⟩
  · rw [xWG_eq hβ hn he (corner k) 0, hT, h0]; rfl
  · rw [xWG_eq hβ hn he (corner k + E 0) 0, hT2, h20]; rfl

/-- **The finite-volume dyadic step for `G`.** -/
theorem dyadic_torus_decayG (β : ℝ) (hβ : 0 ≤ β) (n : ℕ)
    (hp2 : PeriodicState.IsPow2 n) (hn2 : 2 ≤ n)
    (hseed : TorusDoubling.defectWG G 4 (wilsonDensityG G) β n ≤ 1 / 1000)
    (x : C(GibbsSpec.IConf G, ℝ))
    (hx : x ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) 0 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in ((periodicUltraG G β : Ultrafilter ℕ) : Filter ℕ),
      torusConnG G 0 0 β j x n ≤ 1 / 2 * torusConnG G 0 0 β j x 0 + ε := by
  have hxh : x ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) 0 0 := (Submodule.mem_inf.mp hx).1
  obtain ⟨R0, hR0⟩ := winLocalG_of_mem hxh
  set R := 2 * R0 with hRdef
  have hRw : WinLocalG R x := hR0.mono (by omega)
  have hRe : Even R := ⟨R0, by omega⟩
  obtain ⟨C, hC⟩ := InfiniteLattice.bounded_of_continuous x.continuous
  set B := max C 1 with hBdef
  have hB1 : 1 ≤ B := le_max_right _ _
  have hCB : ∀ U, |x U| ≤ B := fun U => (hC U).trans (le_max_left _ _)
  have he : Even n := by
    obtain ⟨b, hb⟩ := hp2
    have hb1 : 1 ≤ b := by
      by_contra h0; have : b = 0 := by omega
      rw [hb, this] at hn2; norm_num at hn2
    exact ⟨2 ^ (b - 1), by rw [hb, ← two_mul, ← pow_succ', Nat.sub_add_cancel hb1]⟩
  obtain ⟨a, ha⟩ : ∃ a, n = 2 ^ (a + 1) := by
    obtain ⟨b, hb⟩ := hp2
    have hb1 : 1 ≤ b := by
      by_contra h0; have : b = 0 := by omega
      rw [hb, this] at hn2; norm_num at hn2
    exact ⟨b - 1, by rw [hb, Nat.sub_add_cancel hb1]⟩
  have hfr := factRepG (G := G) hβ hn2 he
  have hp := positive_of_facts hfr
  have hxS := DoublingSharp.positiveS_of_facts hfr
  have hΔ : Δ (xWG G n β) (corner 0) ≤ 1 / 1000 := by rw [Δ_corner0G]; exact hseed
  set δ : ℝ := min (1 / 8) ((ε / (100 * B ^ 2)) ^ 2 / 2) with hδdef
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨K0, hK0⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  set J0 := 2 ^ (K0 + 2) * n + R + R + n with hJ0
  filter_upwards [periodicUltraG_seed_mem G β a,
    (periodicUltraG_le_atTop G β) (eventually_ge_atTop J0)] with j hjk hjJ
  obtain ⟨k, hk⟩ := hjk
  rw [← ha] at hk
  have hkK : K0 + 2 ≤ k := by
    by_contra hlt
    have h1 : 2 ^ k ≤ 2 ^ (K0 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ k * n ≤ 2 ^ (K0 + 1) * n := Nat.mul_le_mul_right n h1
    have h3 : 2 ^ (K0 + 2) * n = 2 * (2 ^ (K0 + 1) * n) := by rw [pow_succ]; ring
    omega
  have hhe : Even (j + 1) := by
    obtain ⟨t, ht⟩ : ∃ t, 2 ^ k = 4 * t := ⟨2 ^ (k - 2), by
      rw [show k = (k - 2) + 2 by omega, pow_add]; norm_num; ring⟩
    rw [ht] at hk
    exact ⟨t * n, by nlinarith⟩
  have hwin : R + n + R ≤ j + 1 := by
    have : n ≤ 2 ^ (K0 + 2) * n := Nat.le_mul_of_pos_left n (Nat.two_pow_pos _)
    omega
  have hkn : 2 ^ k * n / 2 = j + 1 := by omega
  set M := 2 * j + 1 with hMdef
  have hSt := step_wtG (G := G) (M := M) hβ
  have hkc : Continuous (Function.uncurry (kern (hAG G 0 (Tc M)) (wtG G M β))) := by
    rw [kern_wtG]; exact continuous_kTG β
  have hkb := abs_kern_le (ν := hAG G 0 (Tc M)) hSt.le_one
  have hks : ∀ y z : SlG G M, kern (hAG G 0 (Tc M)) (wtG G M β) y z
      = kern (hAG G 0 (Tc M)) (wtG G M β) z y := by
    rw [kern_wtG]; exact kTG_symm β
  have hpos : 0 < ‖kernelCLM (kern (hAG G 0 (Tc M)) (wtG G M β)) 1 (KernelEigen.kmeas hkc)
      zero_le_one hkb (hSG G 0 (Tc M)) (hSG G 0 (Tc M))‖ := by
    refine norm_pos_iff.mpr (kernelCLM_ne_zero _ _ _ _ _ _ _
      (RectTransfer.kTmin_pos (μ := 0) (T := Tc M) β) (fun y z => ?_))
    rw [kern_wtG]; exact kTG_lower hβ y z
  obtain ⟨φ, hφm, ⟨Bφ, hφb⟩, hφ1, c, hc, heig⟩ :=
    KernelEigen.exists_eigen (μ := hSG G 0 (Tc M)) hkc zero_le_one hkb hks hpos
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hc; linarith
  have hpf := powerFacts (μ := hSG G 0 (Tc M)) (KernelEigen.kmeas hkc) zero_le_one hkb hks hφm hφb
    hφ1 heig hc hc0 (j + 1) (by omega)
  obtain ⟨h1, h2⟩ := xWG_corner (G := G) hβ hn2 he hk
  have hexc := DoublingSharp.excited_le_corner_sharp hxS hp hΔ k hpf h1 h2
  have hgap := KernelGap.gap_of_excited (KernelEigen.kmeas hkc) zero_le_one hkb hks hφm hφb hφ1
    heig hc hc0 k n (by omega) he (by rw [hkn]; exact hexc)
  set s := KernelPower.excited (hSG G 0 (Tc M)) (kern (hAG G 0 (Tc M)) (wtG G M β)) c φ (j + 1)
    with hsdef'
  have hlp : 0 < |c| := abs_pos.mpr hc0
  have hs0 : 0 ≤ s := div_nonneg (hs_nonneg _) (by positivity)
  have hsk : s ≤ (1 / 2) ^ K0 := by
    refine hexc.trans ?_
    have : K0 ≤ 2 ^ k := by
      have := Nat.lt_two_pow_self (n := k); omega
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) this
  have hsδ : s ≤ δ := (hsk.trans hK0.le)
  have hs8 : s ≤ 1 / 8 := hsδ.trans (min_le_left _ _)
  have hsdef : hs (hSG G 0 (Tc M)) (iter (hSG G 0 (Tc M))
      (rem (kern (hAG G 0 (Tc M)) (wtG G M β)) c φ) j) = s * |c| ^ (2 * (j + 1)) := by
    rw [hsdef']; unfold KernelPower.excited
    rw [show j + 1 - 1 = j by omega]; field_simp
  have hη : 100 * B ^ 2 * Real.sqrt (2 * s) ≤ ε := by
    have hB2 : 0 < 100 * B ^ 2 := by positivity
    have h2s : 2 * s ≤ (ε / (100 * B ^ 2)) ^ 2 := by
      have := hsδ.trans (min_le_right _ _); linarith
    have := Real.sqrt_le_sqrt h2s
    rw [Real.sqrt_sq (by positivity)] at this
    calc 100 * B ^ 2 * Real.sqrt (2 * s) ≤ 100 * B ^ 2 * (ε / (100 * B ^ 2)) :=
          mul_le_mul_of_nonneg_left this hB2.le
      _ = ε := by field_simp
  set θx := (⇑(ReflectionShift.ishiftObsL (G := G) 0))^[R]
    (LatticeReflection.ireflObs 0 0 x) with hθx
  have hW1 : WinLocalG R θx := winLocalG_refl hRw
  have hWs : ∀ d, WinLocalG (R + d) ((⇑(ReflectionShift.ishiftObsL (G := G) 0))^[d] x) :=
    fun d => winLocalG_shift hRw d
  set F₁ : (ℕ → SlG G M) → (ℕ → AxG G M) → ℝ := winFG θx with hF₁def
  set F₂ : (ℕ → SlG G M) → (ℕ → AxG G M) → ℝ := winFG x with hF₂def
  have hrev : ∀ V A, F₁ V A = F₂ (revX R V) (revY (invAG (G := G) (M := M)) R A) :=
    fun V A => winFG_refl hRw V A
  have iF₁ : Ins F₁ B := ⟨measurable_winFG θx, fun V A => by rw [hrev]; exact hCB _⟩
  have iF₂ : Ins F₂ B := ⟨measurable_winFG x, fun V A => hCB _⟩
  have l₁ : LocalUpTo R F₁ := localUpTo_winFG hW1
  have l₂ : LocalUpTo R F₂ := localUpTo_winFG hRw
  have hshiftF : ∀ d, winFG (M := M) ((⇑(ReflectionShift.ishiftObsL (G := G) 0))^[d] x)
      = fun V A => F₂ (sshift V d) (sshift A d) := fun d => by
    funext V A; exact winFG_shift hRw d V A
  have T1 : GaugeWilson.torusStateG G M β (LatticeReflection.ireflObs 0 0 x)
      = Eh (hSG G 0 (Tc M)) (hAG G 0 (Tc M)) (wtG G M β) M F₁ := by
    rw [← torusStateG_iterS M β R, torusStateG_Eh hβ hW1 (by omega)]
  have T2 : ∀ d, R + (R + d) ≤ M → GaugeWilson.torusStateG G M β
      ((⇑(ReflectionShift.ishiftObsL (G := G) 0))^[d] x)
      = Eh (hSG G 0 (Tc M)) (hAG G 0 (Tc M)) (wtG G M β) M
          (fun V A => F₂ (sshift V (R + d)) (sshift A (R + d))) := by
    intro d hd
    rw [← torusStateG_iterS M β R, ← Function.iterate_add_apply,
      torusStateG_Eh hβ (hWs (R + d)) hd, hshiftF]
  have T3 : ∀ d, R + (R + d) ≤ M → GaugeWilson.torusStateG G M β
      (LatticeReflection.ireflObs 0 0 x
        * (⇑(ReflectionShift.ishiftObsL (G := G) 0))^[d] x)
      = Eh (hSG G 0 (Tc M)) (hAG G 0 (Tc M)) (wtG G M β) M
          (fun V A => F₁ V A * F₂ (sshift V (R + d)) (sshift A (R + d))) := by
    intro d hd
    rw [← torusStateG_iterS M β R, iterS_mulG, ← Function.iterate_add_apply,
      torusStateG_Eh hβ ((hW1.mono (by omega : R ≤ R + (R + d))).mul (hWs (R + d))) hd]
    congr 1; funext V A
    show F₁ V A * winFG ((⇑(ReflectionShift.ishiftObsL (G := G) 0))^[R + d] x) V A = _
    rw [hshiftF]
  have hθ : LatticeReflection.ireflObs (G := G) 0 (2 * (0 : ℤ))
      = LatticeReflection.ireflObs 0 0 := by norm_num
  have key := chain_decay hSt (invAG (G := G) (M := M)) mp_invAG invAG_invAG
    (fun V A V' => wtG_symm β V A V') hφm hφb hφ1 heig hc0 j hs0 hs8 hsdef hhe
    (L := M) (by omega) he hc hgap hRe hwin iF₁ iF₂ l₁ l₂ hrev
  unfold torusConnG
  rw [hθ, T3 n (by omega), T1, T2 n (by omega), T3 0 (by omega), T2 0 (by omega),
    Nat.add_comm R n, Nat.add_zero]
  linarith

end MassGap.TorusDecayG

#print axioms MassGap.TorusDecayG.dyadic_torus_decayG
