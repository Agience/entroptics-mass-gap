import Mathlib
import MassGap.ChainDecay
import MassGap.TorusChain
import MassGap.DoublingSharp
import MassGap.KernelEigen
import MassGap.PeriodicDyadic
import MassGap.PeriodicReduce
import MassGap.GaugeInvariantAlgebra
import MassGap.WilsonState

/-!
# MassGap.TorusDecay — the finite-volume dyadic step, proved

`dyadic_torus_decay`: at `β ≥ 0`, a power-of-two seed `n ≥ 2` with
`16 log ZR(n⁴) − log ZR((2n)⁴) ≤ 1/1000`, every gauge-invariant half-space observable `x` and every
`ε > 0`, eventually along `PeriodicState.periodicUltra hN β`,

    torusConn 0 0 hN β j x n ≤ ½ · torusConn 0 0 hN β j x 0 + ε.

The torus of extent `2j + 2` in the ultrafilter is a dyadic corner `2^k n`
(`PeriodicDyadic.periodicUltra_seed_mem`). On it the doubling recursion gives both the transfer gap
`‖Kⁿ f‖ ≤ ½‖K‖ⁿ‖f‖` on the vacuum complement (`KernelGap.gap_of_excited`) and the excited weight
`s ≤ (1/2)^{2^k}` of the torus itself (`DoublingSharp.excited_le_corner_sharp`). The torus state of the
window observables is a ratio of closed hidden-variable chains (`TorusChain.torusState_winF`), and
`ChainDecay.chain_decay` bounds the connected pairing by the gap up to `100 B² √(2s)`, which the
dyadic extents drive below `ε`.
-/

namespace MassGap.TorusDecay

open MeasureTheory Real Filter MassGap MassGap.RectWilson MassGap.RectTransfer MassGap.KernelPower
  MassGap.HiddenChain MassGap.ChainClosing MassGap.ChainReduce MassGap.ChainDecay
  MassGap.TorusChain MassGap.DoublingRecursion MassGap.DoublingWilson MassGap.DoublingPower
  MassGap.SlabKernelOperator

set_option linter.unusedSectionVars false

variable {N : ℕ}

/-- The unit shift along `0`, iterated, is multiplicative. -/
theorem iterS_mul (R : ℕ) (f g : C(GibbsSpec.IConf (SUN.SU N), ℝ)) :
    (⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[R] (f * g)
      = (⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[R] f
        * (⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[R] g := by
  ext U
  rw [ContinuousMap.mul_apply, shiftObs_iter, shiftObs_iter, shiftObs_iter, ContinuousMap.mul_apply]

theorem torusState_iterS (hN : N ≠ 0) (M : ℕ) (β : ℝ) (R : ℕ) (g : C(GibbsSpec.IConf (SUN.SU N), ℝ)) :
    PeriodicState.torusState hN M β ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[R] g)
      = PeriodicState.torusState hN M β g := by
  induction R with
  | zero => rfl
  | succ R ih => rw [Function.iterate_succ_apply', PeriodicState.torusState_shift, ih]

/-- The torus chain is the abstract closed chain. -/
theorem Zc_eq {M : ℕ} {β : ℝ} (F : (ℕ → Sl M N) → (ℕ → Ax M N) → ℝ) :
    Zc M N β F = Zh (hS 0 (Tc M) N) (hA 0 (Tc M) N) (wt M N β) M F := by
  unfold Zc Zh; rw [kern_wt]

theorem torusState_Eh (hN : N ≠ 0) {M : ℕ} {β : ℝ} (hβ : 0 ≤ β) {w : ℕ}
    {g : C(GibbsSpec.IConf (SUN.SU N), ℝ)} (hg : WinLocal w g) (hw : w ≤ M) :
    PeriodicState.torusState hN M β g
      = Eh (hS 0 (Tc M) N) (hA 0 (Tc M) N) (wt M N β) M (winF g) := by
  rw [torusState_winF hN hβ hg hw, Zc_eq, Zc_eq]; rfl

/-- The step weight of the cubic torus as an abstract step. -/
theorem step_wt (hN : N ≠ 0) {M : ℕ} {β : ℝ} (hβ : 0 ≤ β) : Step (wt M N β) :=
  ⟨wmeas_wt β, wt_nonneg β, abs_wt_le hN hβ⟩

theorem xW_corner (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) {k j : ℕ}
    (hk : 2 * j + 2 = 2 ^ k * n) :
    xW N n β (corner k) = Real.log (traceSeq (hS 0 (Tc (2 * j + 1)) N)
        (kern (hA 0 (Tc (2 * j + 1)) N) (wt (2 * j + 1) N β)) (2 * (j + 1))) ∧
      xW N n β (corner k + E 0) = Real.log (traceSeq (hS 0 (Tc (2 * j + 1)) N)
        (kern (hA 0 (Tc (2 * j + 1)) N) (wt (2 * j + 1) N β)) (2 * (2 * (j + 1)))) := by
  have hL : ext n (corner k) = Lc (2 * j + 1) := by
    funext i; simp only [ext, corner, Lc]; omega
  have hT : tr (ext n (corner k)) 0 = Tc (2 * j + 1) := by rw [hL]
  have hT2 : tr (ext n (corner k + E 0)) 0 = Tc (2 * j + 1) := by rw [tr_ext_add, hT]
  have h0 : ext n (corner k) 0 = 2 * (j + 1) := by rw [hL]; simp only [Lc]; omega
  have h20 : ext n (corner k + E 0) 0 = 2 * (2 * (j + 1)) := by rw [ext_add_self, h0]
  rw [kern_wt]
  refine ⟨?_, ?_⟩
  · rw [xW_eq hN hβ hn he (corner k) 0, hT, h0]; rfl
  · rw [xW_eq hN hβ hn he (corner k + E 0) 0, hT2, h20]; rfl

/-- **The finite-volume dyadic step.** -/
theorem dyadic_torus_decay (hN : N ≠ 0) (β : ℝ) (hβ : 0 ≤ β) (n : ℕ)
    (hp2 : PeriodicState.IsPow2 n) (hn2 : 2 ≤ n)
    (hseed : 16 * Real.log (RectWilson.ZR (fun _ => n) N β)
      - Real.log (RectWilson.ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (x : C(GibbsSpec.IConf (SUN.SU N), ℝ))
    (hx : x ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := SUN.SU N) 0 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in ((PeriodicState.periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ),
      PeriodicReduce.torusConn 0 0 hN β j x n
        ≤ 1 / 2 * PeriodicReduce.torusConn 0 0 hN β j x 0 + ε := by
  -- the window of `x`
  have hxh : x ∈ HalfSpaceAlgebra.halfSpaceAlg (G := SUN.SU N) 0 0 := (Submodule.mem_inf.mp hx).1
  obtain ⟨R0, hR0⟩ := winLocal_of_mem hxh
  set R := 2 * R0 with hRdef
  have hRw : WinLocal R x := hR0.mono (by omega)
  have hRe : Even R := ⟨R0, by omega⟩
  obtain ⟨C, hC⟩ := InfiniteLattice.bounded_of_continuous x.continuous
  set B := max C 1 with hBdef
  have hB1 : 1 ≤ B := le_max_right _ _
  have hCB : ∀ U, |x U| ≤ B := fun U => (hC U).trans (le_max_left _ _)
  -- the doubling recursion
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
  have hfr := factRep hN hβ hn2 he
  have hp := positive_of_facts hfr
  have hxS := DoublingSharp.positiveS_of_facts hfr
  have hΔ : Δ (xW N n β) (corner 0) ≤ 1 / 1000 := by rw [Δ_corner0]; exact hseed
  -- the dyadic depth needed for `ε`
  set δ : ℝ := min (1 / 8) ((ε / (100 * B ^ 2)) ^ 2 / 2) with hδdef
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨K0, hK0⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  set J0 := 2 ^ (K0 + 2) * n + R + R + n with hJ0
  filter_upwards [PeriodicDyadic.periodicUltra_seed_mem hN β a,
    (PeriodicState.periodicUltra_le hN β) (eventually_ge_atTop J0)] with j hjk hjJ
  obtain ⟨k, hk⟩ := hjk
  rw [← ha] at hk
  -- the depth `k` is large
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
  -- the transfer kernel of this torus
  set M := 2 * j + 1 with hMdef
  have hSt := step_wt (M := M) hN hβ
  have hkc : Continuous (Function.uncurry (kern (hA 0 (Tc M) N) (wt M N β))) := by
    rw [kern_wt]; exact continuous_kT β
  have hkb := abs_kern_le (ν := hA 0 (Tc M) N) hSt.le_one
  have hks : ∀ y z : Sl M N, kern (hA 0 (Tc M) N) (wt M N β) y z
      = kern (hA 0 (Tc M) N) (wt M N β) z y := by
    rw [kern_wt]; exact kT_symm β
  have hpos : 0 < ‖kernelCLM (kern (hA 0 (Tc M) N) (wt M N β)) 1 (KernelEigen.kmeas hkc)
      zero_le_one hkb (hS 0 (Tc M) N) (hS 0 (Tc M) N)‖ := by
    refine norm_pos_iff.mpr (kernelCLM_ne_zero _ _ _ _ _ _ _ (kTmin_pos (μ := 0) (T := Tc M) β)
      (fun y z => ?_))
    rw [kern_wt]; exact kT_lower hN hβ y z
  obtain ⟨φ, hφm, ⟨Bφ, hφb⟩, hφ1, c, hc, heig⟩ :=
    KernelEigen.exists_eigen (μ := hS 0 (Tc M) N) hkc zero_le_one hkb hks hpos
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hc; linarith
  have hpf := powerFacts (μ := hS 0 (Tc M) N) (KernelEigen.kmeas hkc) zero_le_one hkb hks hφm hφb
    hφ1 heig hc hc0 (j + 1) (by omega)
  obtain ⟨h1, h2⟩ := xW_corner hN hβ hn2 he hk
  have hexc := DoublingSharp.excited_le_corner_sharp hxS hp hΔ k hpf h1 h2
  have hgap := KernelGap.gap_of_excited (KernelEigen.kmeas hkc) zero_le_one hkb hks hφm hφb hφ1
    heig hc hc0 k n (by omega) he (by rw [hkn]; exact hexc)
  -- the excited weight of the torus
  set s := KernelPower.excited (hS 0 (Tc M) N) (kern (hA 0 (Tc M) N) (wt M N β)) c φ (j + 1) with hsdef'
  have hlp : 0 < |c| := abs_pos.mpr hc0
  have hs0 : 0 ≤ s := div_nonneg (hs_nonneg _) (by positivity)
  have hsk : s ≤ (1 / 2) ^ K0 := by
    refine hexc.trans ?_
    have : K0 ≤ 2 ^ k := by
      have := Nat.lt_two_pow_self (n := k); omega
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) this
  have hsδ : s ≤ δ := (hsk.trans hK0.le)
  have hs8 : s ≤ 1 / 8 := hsδ.trans (min_le_left _ _)
  have hsdef : hs (hS 0 (Tc M) N) (iter (hS 0 (Tc M) N)
      (rem (kern (hA 0 (Tc M) N) (wt M N β)) c φ) j) = s * |c| ^ (2 * (j + 1)) := by
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
  -- the observables as window insertions
  set θx := (⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[R]
    (LatticeReflection.ireflObs 0 0 x) with hθx
  have hW1 : WinLocal R θx := winLocal_refl hRw
  have hWs : ∀ d, WinLocal (R + d) ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[d] x) :=
    fun d => winLocal_shift hRw d
  set F₁ : (ℕ → Sl M N) → (ℕ → Ax M N) → ℝ := winF θx with hF₁def
  set F₂ : (ℕ → Sl M N) → (ℕ → Ax M N) → ℝ := winF x with hF₂def
  have hrev : ∀ V A, F₁ V A = F₂ (revX R V) (revY (invA (M := M) (N := N)) R A) :=
    fun V A => winF_refl hRw V A
  have iF₁ : Ins F₁ B := ⟨measurable_winF θx, fun V A => by rw [hrev]; exact hCB _⟩
  have iF₂ : Ins F₂ B := ⟨measurable_winF x, fun V A => hCB _⟩
  have l₁ : LocalUpTo R F₁ := localUpTo_winF hW1
  have l₂ : LocalUpTo R F₂ := localUpTo_winF hRw
  have hshiftF : ∀ d, winF (M := M) ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[d] x)
      = fun V A => F₂ (sshift V d) (sshift A d) := fun d => by
    funext V A; exact winF_shift hRw d V A
  -- the torus expectations as closed chains
  have T1 : PeriodicState.torusState hN M β (LatticeReflection.ireflObs 0 0 x)
      = Eh (hS 0 (Tc M) N) (hA 0 (Tc M) N) (wt M N β) M F₁ := by
    rw [← torusState_iterS hN M β R, torusState_Eh hN hβ hW1 (by omega)]
  have T2 : ∀ d, R + (R + d) ≤ M → PeriodicState.torusState hN M β
      ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[d] x)
      = Eh (hS 0 (Tc M) N) (hA 0 (Tc M) N) (wt M N β) M
          (fun V A => F₂ (sshift V (R + d)) (sshift A (R + d))) := by
    intro d hd
    rw [← torusState_iterS hN M β R, ← Function.iterate_add_apply,
      torusState_Eh hN hβ (hWs (R + d)) hd, hshiftF]
  have T3 : ∀ d, R + (R + d) ≤ M → PeriodicState.torusState hN M β
      (LatticeReflection.ireflObs 0 0 x
        * (⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[d] x)
      = Eh (hS 0 (Tc M) N) (hA 0 (Tc M) N) (wt M N β) M
          (fun V A => F₁ V A * F₂ (sshift V (R + d)) (sshift A (R + d))) := by
    intro d hd
    rw [← torusState_iterS hN M β R, iterS_mul, ← Function.iterate_add_apply,
      torusState_Eh hN hβ ((hW1.mono (by omega : R ≤ R + (R + d))).mul (hWs (R + d))) hd]
    congr 1; funext V A
    show F₁ V A * winF ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[R + d] x) V A = _
    rw [hshiftF]
  have hθ : LatticeReflection.ireflObs (G := SUN.SU N) 0 (2 * (0 : ℤ))
      = LatticeReflection.ireflObs 0 0 := by norm_num
  have key := chain_decay hSt (invA (M := M) (N := N)) mp_invA invA_invA
    (fun V A V' => wt_symm β V A V') hφm hφb hφ1 heig hc0 j hs0 hs8 hsdef hhe
    (L := M) (by omega) he hc hgap hRe hwin iF₁ iF₂ l₁ l₂ hrev
  unfold PeriodicReduce.torusConn
  rw [hθ, T3 n (by omega), T1, T2 n (by omega), T3 0 (by omega), T2 0 (by omega),
    Nat.add_comm R n, Nat.add_zero]
  linarith

#print axioms dyadic_torus_decay

end MassGap.TorusDecay
