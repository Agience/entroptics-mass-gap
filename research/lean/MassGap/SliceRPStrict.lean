import Mathlib
import MassGap.TorusChain
import MassGap.SliceKernelPower

/-!
# MassGap.SliceRPStrict — strict reflection positivity of one-slice observables on the torus

On the periodic cubic torus of extent `2M′ + 2`, an observable read on the spatial links of one
slice has strictly positive reflected two-point value under the site reflection at `x₀ = 0`.

* `Qr q r` — the `ℤ⁴` observable that reads the spatial links of the slice at time `r` and applies
  `q : C(Sl M N, ℝ)` to them. It is continuous and `WinLocal r` (`winLocal_Qr`); on the chain
  variables it is `q (V r)` (`winF_Qr`).
* `Zc_pair` — the closed torus chain with insertions `q(V 0) q(V (i+1))`, total length
  `M = i + 1 + b`, is `∫∫ q(x) q(y) kT^{∗(i+1)}(x,y) kT^{∗(b+1)}(y,x)`: `chain_split` at `i + 1`,
  `chain_end_kern` on the tail, `chain_mul_start` and `chain_end_iter` on the head, and `kern_wt`.
* `torusState_refl_Qr_pos` — for `0 < β`, `N ≠ 0`, `1 ≤ r ≤ M′`, and `q` continuous, gauge
  invariant (`SliceKernelDefinite.GaugeInv`) and nonzero:
  `0 < torusState hN (2M′+1) β (ireflObs 0 0 (Qr q r) * Qr q r)`. Shift invariance carries the pair
  to the window `[0, 2r]` (`winF_refl`, `winF_shift`), `torusState_winF` writes the state as
  `Zc(q(V 0) q(V 2r)) / Zc 1`, and both chains are `SliceKernelPower.sand_square_pos` at
  separations `2r` and `2M′ + 2 − 2r` (the denominator at `q = 1`).

Classification: this is finite-torus content for one class of observables (those local on the
spatial links of one slice) inside `TorusCapstone.TorusRefPos`; it is not the pinned `LagOnePos`
and discharges no ledger hypothesis. After `TorusRefPos`, `hpos` still needs `RefPassage`
(uniform in the volume). Gauge invariance is taken on the slice function `q` (`gact` on `Sl`). For
`q` built from the plaquettes of one slice it is checked directly, plaquette by plaquette (each is
conjugated, as in `SliceKernelDefinite.sp_gact`); no four-dimensional gauge transformation enters.
The off-diagonal pairs `⟨θ Q_r · Q_{r'}⟩ ≥ 0` and the strict positivity of a sum of slices are
`TorusRefPosPlane.torusState_refl_Qr_pair_nonneg` and `TorusRefPosPlane.torusState_refl_sum_pos`.
-/

namespace MassGap.SliceRPStrict

open MeasureTheory MassGap MassGap.RectWilson MassGap.RectTransfer MassGap.HiddenChain
  MassGap.KernelPower MassGap.TorusChain

set_option linter.unusedSectionVars false

variable {M N : ℕ}

/-! ## The one-slice observable -/

/-- The `ℤ⁴` site at time `t` with transverse coordinates `y`. -/
def site (t : ℤ) (y : TT 0 (Tc M)) : Fin 4 → ℤ :=
  fun i => if h : i = 0 then t else ((y ⟨i, h⟩ : ℕ) : ℤ)

theorem site_zero (t : ℤ) (y : TT 0 (Tc M)) : site t y 0 = t := by
  unfold site; rw [dif_pos rfl]

theorem perpI_site (t : ℤ) (y : TT 0 (Tc M)) : perpI M (site t y) = y := by
  funext j
  apply Fin.ext
  have hj : site (M := M) t y j.1 = ((y j : ℕ) : ℤ) := by unfold site; rw [dif_neg j.2]
  show ((site (M := M) t y j.1) % ((M : ℤ) + 1)).toNat = (y j : ℕ)
  rw [hj]
  have hlt : (y j : ℕ) < M + 1 := (y j).isLt
  rw [Int.emod_eq_of_lt (by positivity) (by omega)]
  simp

/-- The spatial links of the slice at time `t` of a `ℤ⁴` configuration. -/
def readSl (t : ℤ) (U : GibbsSpec.IConf (SUN.SU N)) : Sl M N := fun p => U (p.1.1, site t p.2)

theorem continuous_readSl (t : ℤ) : Continuous (readSl (M := M) (N := N) t) :=
  continuous_pi fun _ => continuous_apply _

/-- `q` read on the spatial links of the slice at time `r`. -/
noncomputable def Qr (q : C(Sl M N, ℝ)) (r : ℕ) : C(GibbsSpec.IConf (SUN.SU N), ℝ) :=
  ⟨fun U => q (readSl (r : ℤ) U), q.continuous.comp (continuous_readSl _)⟩

theorem Qr_apply (q : C(Sl M N, ℝ)) (r : ℕ) (U : GibbsSpec.IConf (SUN.SU N)) :
    Qr q r U = q (readSl (r : ℤ) U) := rfl

/-- `Qr q r` reads only spatial links at time `r`. -/
theorem winLocal_Qr (q : C(Sl M N, ℝ)) (r : ℕ) : WinLocal r (Qr q r) := by
  intro U U' h
  show q (readSl (r : ℤ) U) = q (readSl (r : ℤ) U')
  congr 1; funext p
  have hs : site (M := M) (r : ℤ) p.2 0 = r := site_zero _ _
  refine h _ ⟨?_, ?_, fun h0 => absurd h0 p.1.2⟩
  · show (0 : ℤ) ≤ site (M := M) (r : ℤ) p.2 0
    rw [hs]; positivity
  · show site (M := M) (r : ℤ) p.2 0 ≤ (r : ℤ)
    rw [hs]

/-- On the chain variables `Qr q r` is `q` of the `r`-th slice. -/
theorem winF_Qr (q : C(Sl M N, ℝ)) (r : ℕ) (V : ℕ → Sl M N) (A : ℕ → Ax M N) :
    winF (Qr q r) V A = q (V r) := by
  show q (readSl (r : ℤ) (cfg M N V A)) = q (V r)
  congr 1; funext p
  show cfg M N V A (p.1.1, site (M := M) (r : ℤ) p.2) = V r p
  have hs : site (M := M) (r : ℤ) p.2 0 = r := site_zero _ _
  rw [cfg_sp (V := V) (A := A) (l := (p.1.1, site (M := M) (r : ℤ) p.2)) p.1.2
    (by show (0 : ℤ) ≤ site (M := M) (r : ℤ) p.2 0; rw [hs]; positivity)]
  show V (site (M := M) (r : ℤ) p.2 0).toNat (⟨p.1.1, p.1.2⟩, perpI M (site (M := M) (r : ℤ) p.2))
    = V r p
  rw [hs, perpI_site, Int.toNat_natCast]

/-! ## The two-insertion closed chain -/

/-- **The two-insertion closed chain is the two-insertion kernel trace.** For `M = i + 1 + b`,
`Zc(q(V 0) q(V (i+1))) = ∫∫ q(x) q(y) kT^{∗(i+1)}(x,y) kT^{∗(b+1)}(y,x)`. -/
theorem Zc_pair (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (q : C(Sl M N, ℝ)) (i b : ℕ)
    (hM : M = i + 1 + b) :
    Zc M N β (fun V _ => q (V 0) * q (V (i + 1)))
      = ∫ x, ∫ y, q x * q y * (iter (hS 0 (Tc M) N) (kT 0 (Tc M) N β) i x y
          * iter (hS 0 (Tc M) N) (kT 0 (Tc M) N β) b y x) ∂(hS 0 (Tc M) N) ∂(hS 0 (Tc M) N) := by
  subst hM
  have hw := wmeas_wt (M := i + 1 + b) (N := N) β
  have hwb := abs_wt_le (M := i + 1 + b) hN hβ
  have hK := kern_wt (M := i + 1 + b) (N := N) β
  unfold Zc
  congr 1; funext x
  dsimp only
  have hl : LocalUpTo (i + 1)
      (fun (V : ℕ → Sl (i + 1 + b) N) (_ : ℕ → Ax (i + 1 + b) N) => q (V 0) * q (V (i + 1))) :=
    fun V V' A A' hV _ => by
      show q (V 0) * q (V (i + 1)) = q (V' 0) * q (V' (i + 1))
      rw [hV 0 (Nat.zero_le _), hV (i + 1) le_rfl]
  have e1 := chain_split (μ := hS 0 (Tc (i + 1 + b)) N) (ν := hA 0 (Tc (i + 1 + b)) N)
    (w := wt (i + 1 + b) N β) (i + 1) b
    (fun V _ => kT 0 (Tc (i + 1 + b)) N β (V b) x) x hl
  simp only [sshift, Nat.add_comm b (i + 1)] at e1
  have e2 : ∀ y, chain (hS 0 (Tc (i + 1 + b)) N) (hA 0 (Tc (i + 1 + b)) N) (wt (i + 1 + b) N β) b
      (fun V _ => kern (hA 0 (Tc (i + 1 + b)) N) (wt (i + 1 + b) N β) (V b) x) y
      = iter (hS 0 (Tc (i + 1 + b)) N) (kern (hA 0 (Tc (i + 1 + b)) N) (wt (i + 1 + b) N β)) b y x :=
    fun y => chain_end_kern (μ := hS 0 (Tc (i + 1 + b)) N) (ν := hA 0 (Tc (i + 1 + b)) N)
      (w := wt (i + 1 + b) N β) x b y
  rw [hK] at e2
  rw [e1]
  simp only [e2]
  have e3 := chain_mul_start (μ := hS 0 (Tc (i + 1 + b)) N) (ν := hA 0 (Tc (i + 1 + b)) N)
    (w := wt (i + 1 + b) N β) (⇑q) (i + 1)
    (fun V _ => q (V (i + 1)) * iter (hS 0 (Tc (i + 1 + b)) N) (kT 0 (Tc (i + 1 + b)) N β) b
      (V (i + 1)) x) x
  simp only [← mul_assoc] at e3
  rw [e3]
  have hki := (bdd_kT (μ := 0) (T := Tc (i + 1 + b)) hN hβ).iter (μ := hS 0 (Tc (i + 1 + b)) N) b
  obtain ⟨Ci, hCi⟩ := hki.bdd
  have hgc : Continuous fun z => q z
      * iter (hS 0 (Tc (i + 1 + b)) N) (kT 0 (Tc (i + 1 + b)) N β) b z x :=
    q.continuous.mul ((SliceKernelPower.continuous_iter (μ := 0) (T := Tc (i + 1 + b)) (N := N)
      β b).comp (continuous_id.prodMk continuous_const))
  have hgb : ∀ z, |q z * iter (hS 0 (Tc (i + 1 + b)) N) (kT 0 (Tc (i + 1 + b)) N β) b z x|
      ≤ ‖q‖ * Ci := fun z =>
    abs_mul_le_of (by simpa [Real.norm_eq_abs] using q.norm_coe_le_norm z) (hCi z x)
  have e4 := chain_end_iter (μ := hS 0 (Tc (i + 1 + b)) N) (ν := hA 0 (Tc (i + 1 + b)) N) hw hwb
    hgc.measurable hgb i x
  rw [hK] at e4
  rw [e4, ← integral_const_mul]
  congr 1; funext y
  ring

/-- The torus normalisation as the two-insertion chain at `q = 1`. -/
theorem Zc_one (β : ℝ) (i : ℕ) :
    Zc M N β (fun _ _ => 1)
      = Zc M N β (fun V _ => (1 : C(Sl M N, ℝ)) (V 0) * (1 : C(Sl M N, ℝ)) (V (i + 1))) := by
  congr 1; funext V A; simp

/-! ## Strict positivity -/

theorem torusState_shift_iter (hN : N ≠ 0) (M : ℕ) (β : ℝ) (d : ℕ)
    (f : C(GibbsSpec.IConf (SUN.SU N), ℝ)) :
    PeriodicState.torusState hN M β ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[d] f)
      = PeriodicState.torusState hN M β f := by
  induction d with
  | zero => rfl
  | succ d ih => rw [Function.iterate_succ_apply', PeriodicState.torusState_shift, ih]

/-- **Strict reflection positivity of a one-slice observable on the torus.** At `N ≠ 0`, `0 < β`,
`1 ≤ r ≤ M′`, for `q` continuous, gauge invariant and nonzero on the spatial links of one slice,
`0 < ⟨θ Q_r · Q_r⟩` on the torus of extent `2M′ + 2`, `Q_r = Qr q r`. -/
theorem torusState_refl_Qr_pos (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β) {M' r : ℕ} (hr : 1 ≤ r)
    (hrM : r ≤ M') (q : C(Sl (2 * M' + 1) N, ℝ)) (hq : SliceKernelDefinite.GaugeInv ⇑q)
    (hq0 : q ≠ 0) :
    0 < PeriodicState.torusState hN (2 * M' + 1) β
      (LatticeReflection.ireflObs 0 0 (Qr q r) * Qr q r) := by
  rw [← torusState_shift_iter hN (2 * M' + 1) β r]
  have hprod : (⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[r]
        (LatticeReflection.ireflObs 0 0 (Qr q r) * Qr q r)
      = (⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[r]
          (LatticeReflection.ireflObs 0 0 (Qr q r))
        * (⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[r] (Qr q r) := by
    ext U; simp only [ContinuousMap.mul_apply, shiftObs_iter]
  have hQ := winLocal_Qr q r
  have hloc := ((winLocal_refl hQ).mono (Nat.le_add_right r r)).mul (winLocal_shift hQ r)
  rw [hprod, torusState_winF hN hβ.le hloc (by omega)]
  have hw : winF (M := 2 * M' + 1) ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[r]
          (LatticeReflection.ireflObs 0 0 (Qr q r))
        * (⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[r] (Qr q r))
      = fun V _ => q (V 0) * q (V (r + r)) := by
    funext V A
    show winF ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[r]
          (LatticeReflection.ireflObs 0 0 (Qr q r))) V A
        * winF ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[r] (Qr q r)) V A = _
    rw [winF_refl hQ, winF_shift hQ, winF_Qr, winF_Qr]
    simp [revX, sshift]
  rw [hw]
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  set m := M' - (r' + 1) with hm
  have hM : 2 * M' + 1 = r' + r' + 1 + 1 + (m + m + 1) := by omega
  rw [show r' + 1 + (r' + 1) = r' + r' + 1 + 1 by omega, Zc_one β (r' + r' + 1),
    Zc_pair hN hβ.le q _ _ hM, Zc_pair hN hβ.le 1 _ _ hM]
  have h1 : (1 : C(Sl (2 * M' + 1) N, ℝ)) ≠ 0 := fun h => by
    have := congrArg (fun f : C(Sl (2 * M' + 1) N, ℝ) => f (fun _ => 1)) h
    simp at this
  exact div_pos (SliceKernelPower.sand_square_pos hN hβ r' m q hq hq0)
    (SliceKernelPower.sand_square_pos hN hβ r' m 1 (fun _ _ => rfl) h1)

end MassGap.SliceRPStrict

#print axioms MassGap.SliceRPStrict.perpI_site
#print axioms MassGap.SliceRPStrict.winLocal_Qr
#print axioms MassGap.SliceRPStrict.winF_Qr
#print axioms MassGap.SliceRPStrict.Zc_pair
#print axioms MassGap.SliceRPStrict.Zc_one
#print axioms MassGap.SliceRPStrict.torusState_shift_iter
#print axioms MassGap.SliceRPStrict.torusState_refl_Qr_pos
