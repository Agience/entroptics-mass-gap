import MassGap.PurityCharDecomp
import MassGap.CharacterExpansion

/-!
# MassGap.PurityKernelSeries — the eigenvalues of the Wilson kernel sum to its value at the identity

Appendix C of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and
S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`)
expands the class function `k_b(g) = exp(b Re Tr U(g) / dim G)` on a compact gauge group `G` in
irreducible characters with eigenvalues `a_π`; `dim G` is the dimension `d` of the defining
representation `U`. This module proves `Σ_π d_π² a_π = e^b`, the value `k_b(1)`.

* `exists_tensorPow`: `(2 Re Tr U(g))^n` is the character of a continuous unitary representation of
  dimension `(2 dim G)^n`, namely `(U ⊕ Ū)^{⊗n}`.
* `mom n r = ∫ (2 Re Tr U)^n conj χ_r dg`; `exists_mom_eq`: it is a natural number.
* `hasSum_dim_mom`: for a family `F` such that every `IrrRep G` is equivalent to exactly one `F i`,
  `Σ_i dim (F i) · mom n (F i) = (2 dim G)^n`.
* `hasSum_dim_sq_eigenval`: for such `F` and every real `b`,
  `Σ_i dim (F i)² · eigenval k_b (F i) = e^b`, where `eigenval k σ = (∫ k χ_σ(h⁻¹) dh) / dim σ`.
  The proof expands `k_b = Σ_n (b/(2 dim G))^n/n! · (2 Re Tr U)^n`, exchanges sum and integral by
  dominated convergence, and sums the absolutely convergent double series in both orders.
-/

namespace MassGap.PurityKernelSeries

open MeasureTheory MassGap MassGap.CompactGauge MassGap.GaugeGroup MassGap.PurityRepCharacter
  MassGap.PurityConvEigen MassGap.PurityReducible MassGap.PurityPeterWeyl MassGap.PuritySchurCross
  MassGap.PurityCharDecomp

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- `(2 Re Tr U(g))^n` is the character of a continuous unitary representation of dimension
`(2 dim G)^n`, namely `(U ⊕ Ū)^{⊗n}`. -/
theorem exists_tensorPow (n : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (σ : G →* Matrix ι ι ℂ),
      Continuous σ ∧ (∀ g, σ g ∈ Matrix.unitaryGroup ι ℂ) ∧ Fintype.card ι = (2 * dim G) ^ n ∧
        ∀ g, Matrix.trace (σ g) = (((2 * (Matrix.trace (repM G g)).re) ^ n : ℝ) : ℂ) := by
  induction n with
  | zero =>
    refine ⟨Unit, inferInstance, inferInstance, 1,
      continuous_const.congr fun g => (MonoidHom.one_apply g).symm,
      fun g => by rw [MonoidHom.one_apply]; exact one_mem _, by simp, fun g => ?_⟩
    simp
  | succ n ih =>
    obtain ⟨ι, _, _, σ, hσ, hu, hc, ht⟩ := ih
    refine ⟨(Fin (dim G) ⊕ Fin (dim G)) × ι, inferInstance, inferInstance,
      kron (dsum (repHom G) (conjRep (repHom G))) σ,
      continuous_kron (continuous_dsum continuous_repHom (continuous_conjRep continuous_repHom)) hσ,
      kron_mem (dsum_mem (fun g => repM_mem g) (conjRep_mem fun g => repM_mem g)) hu, ?_,
      fun g => ?_⟩
    · rw [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, hc, pow_succ]
      ring
    · have hD : Matrix.trace (dsum (repHom G) (conjRep (repHom G)) g) =
          ((2 * (Matrix.trace (repM G g)).re : ℝ) : ℂ) := by
        show Matrix.trace (Matrix.fromBlocks (repHom G g) 0 0 (conjRep (repHom G) g)) = _
        rw [← Matrix.mul_one (Matrix.fromBlocks _ _ _ _), ← Matrix.fromBlocks_one,
          trace_fromBlocks_mul, Matrix.mul_one, Matrix.mul_one, trace_conjRep, repHom_apply,
          Complex.add_conj]
      rw [trace_kron, ht g, hD, pow_succ]
      push_cast
      ring

/-- `∫ (2 Re Tr U(g))^n conj χ_r(g) dg`. -/
noncomputable def mom (n : ℕ) (r : IrrRep G) : ℂ :=
  ∫ g, (((2 * (Matrix.trace (repM G g)).re) ^ n : ℝ) : ℂ) *
    starRingEnd ℂ (Matrix.trace (r.τ g)) ∂probHaar G

/-- `mom n r` is the multiplicity `mult σ r` for any `σ` with character `(2 Re Tr U)^n`. -/
theorem mom_eq_mult {ι : Type} [Fintype ι] [DecidableEq ι] {σ : G →* Matrix ι ι ℂ} {n : ℕ}
    (ht : ∀ g, Matrix.trace (σ g) = (((2 * (Matrix.trace (repM G g)).re) ^ n : ℝ) : ℂ))
    (r : IrrRep G) : mom n r = mult σ r := by
  simp only [mom, mult, ht]

open Classical in
/-- `mom n r` is a natural number. -/
theorem exists_mom_eq (n : ℕ) (r : IrrRep G) : ∃ m : ℕ, mom n r = m := by
  obtain ⟨ι, _, _, σ, hσ, hu, -, ht⟩ := exists_tensorPow (G := G) n
  obtain ⟨J, _, R, -, e⟩ := char_decomp hσ hu
  rw [mom_eq_mult ht, mult_eq R e]
  simp only [Finset.sum_boole]
  exact ⟨_, rfl⟩

/-- For a family `F` such that every `IrrRep G` is equivalent to exactly one `F i`,
`Σ_i dim (F i) · mom n (F i) = (2 dim G)^n`. -/
theorem hasSum_dim_mom (n : ℕ) {I : Type*} (F : I → IrrRep G)
    (hF : ∀ r : IrrRep G, ∃! i, Equivalent (F i).τ r.τ) :
    HasSum (fun i => (Fintype.card (F i).κ : ℂ) * mom n (F i)) (((2 * dim G) ^ n : ℕ) : ℂ) := by
  obtain ⟨ι, _, _, σ, hσ, hu, hc, ht⟩ := exists_tensorPow (G := G) n
  have h := finsum_dim_mult hσ hu F hF
  simp only [← mom_eq_mult ht] at h
  rw [hc] at h
  have hfin : (Function.support fun i => (Fintype.card (F i).κ : ℂ) * mom n (F i)).Finite := by
    by_contra hinf
    rw [finsum_of_infinite_support hinf] at h
    exact (pow_pos (Nat.mul_pos two_pos (dim_pos (G := G))) n).ne' (Nat.cast_eq_zero.mp h.symm)
  rw [← h, finsum_eq_sum _ hfin]
  exact hasSum_sum_of_ne_finset_zero fun i hi => by
    rwa [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hi

/-- For a family `F` such that every `IrrRep G` is equivalent to exactly one `F i` and every real
`b`, the kernel `k_b(g) = exp(b Re Tr U(g) / dim G)` satisfies
`Σ_i dim (F i)² · eigenval k_b (F i) = e^b`, the value `k_b(1)`. -/
theorem hasSum_dim_sq_eigenval (b : ℝ) {I : Type*} (F : I → IrrRep G)
    (hF : ∀ r : IrrRep G, ∃! i, Equivalent (F i).τ r.τ) :
    HasSum (fun i => (Fintype.card (F i).κ : ℂ) ^ 2 *
      eigenval (fun g => (Real.exp (b * ((Matrix.trace (repM G g)).re / dim G)) : ℂ)) (F i).τ)
      (Real.exp b) := by
  have hd0 : (0 : ℝ) < dim G := Nat.cast_pos.mpr dim_pos
  obtain ⟨x, hx⟩ : ∃ x : G → ℝ, ∀ g, x g = 2 * (Matrix.trace (repM G g)).re := ⟨_, fun g => rfl⟩
  have hxc : Continuous x := by
    have : x = fun g => 2 * (Matrix.trace (repM G g)).re := funext hx
    rw [this]
    exact continuous_const.mul (Complex.continuous_re.comp continuous_repM.matrix_trace)
  have hxb : ∀ g, |x g| ≤ 2 * (dim G : ℝ) := fun g => by
    rw [hx g, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left (abs_re_trace_repM_le g) zero_le_two
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, ∀ n, c n = (b / (2 * dim G)) ^ n / n.factorial :=
    ⟨_, fun n => rfl⟩
  -- the kernel as a power series in `x`
  have hk : ∀ g, HasSum (fun n => c n * x g ^ n)
      (Real.exp (b * ((Matrix.trace (repM G g)).re / dim G))) := fun g => by
    have e : (fun n => c n * x g ^ n) =
        fun n => (b / (2 * dim G) * x g) ^ n / n.factorial := funext fun n => by
      rw [hc n]
      ring
    have e2 : b * ((Matrix.trace (repM G g)).re / dim G) = b / (2 * dim G) * x g := by
      rw [hx g]
      field_simp
    rw [e, e2]
    exact CharacterExpansion.hasSum_exp_div _
  have hsum : Summable fun n => |c n| * (2 * (dim G : ℝ)) ^ n := by
    refine (CharacterExpansion.hasSum_exp_div (|b / (2 * dim G)| * (2 * dim G))).summable.congr
      fun n => ?_
    have hcn : |c n| = |b / (2 * dim G)| ^ n / n.factorial := by
      rw [hc n, abs_div ((b / (2 * dim G)) ^ n), abs_pow, Nat.abs_cast]
    rw [hcn, div_mul_eq_mul_div, ← mul_pow]
  -- sum and integral exchange for each `F i`
  have hI : ∀ i, HasSum (fun n => (c n : ℂ) * mom n (F i))
      (∫ g, (Real.exp (b * ((Matrix.trace (repM G g)).re / dim G)) : ℂ) *
        starRingEnd ℂ (Matrix.trace ((F i).τ g)) ∂probHaar G) := by
    intro i
    have hχ : Continuous fun g => starRingEnd ℂ (Matrix.trace ((F i).τ g)) :=
      Complex.continuous_conj.comp (F i).cont.matrix_trace
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hχ.continuousOn
    have hmom : ∀ n, (c n : ℂ) * mom n (F i) = ∫ g, (c n : ℂ) * (((x g ^ n : ℝ) : ℂ) *
        starRingEnd ℂ (Matrix.trace ((F i).τ g))) ∂probHaar G := fun n => by
      rw [integral_const_mul]
      congr 1
      simp only [mom, hx]
    simp_rw [hmom]
    refine hasSum_integral_of_dominated_convergence (fun n _ => |c n| * ((2 * dim G) ^ n * C))
      (fun n => ?_) (fun n => ?_) ?_ (integrable_const _) ?_
    · exact (continuous_const.mul ((Complex.continuous_ofReal.comp (hxc.pow n)).mul hχ)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun g => ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_pow]
      gcongr
      · exact hxb g
      · exact hC g (Set.mem_univ g)
    · exact Filter.Eventually.of_forall fun g =>
        (hsum.mul_right C).congr fun n => mul_assoc _ _ _
    · refine Filter.Eventually.of_forall fun g => ?_
      have h := (Complex.hasSum_ofReal.mpr (hk g)).mul_right
        (starRingEnd ℂ (Matrix.trace ((F i).τ g)))
      have e : (fun n => (c n : ℂ) * (((x g ^ n : ℝ) : ℂ) *
          starRingEnd ℂ (Matrix.trace ((F i).τ g)))) =
          fun n => ((c n * x g ^ n : ℝ) : ℂ) * starRingEnd ℂ (Matrix.trace ((F i).τ g)) :=
        funext fun n => by push_cast; ring
      rw [e]
      exact h
  -- the fibre over `F i` sums to `dim (F i)² · eigenval`
  have hfibI : ∀ i, HasSum (fun n => (c n : ℂ) * ((Fintype.card (F i).κ : ℂ) * mom n (F i)))
      ((Fintype.card (F i).κ : ℂ) ^ 2 *
        eigenval (fun g => (Real.exp (b * ((Matrix.trace (repM G g)).re / dim G)) : ℂ))
          (F i).τ) := fun i => by
    have hne : (Fintype.card (F i).κ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
    have hinv : ∀ g, Matrix.trace ((F i).τ g⁻¹) = starRingEnd ℂ (Matrix.trace ((F i).τ g)) :=
      fun g => by
        rw [inv_eq_star (F i).unitary g, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]
        rfl
    have heig : (Fintype.card (F i).κ : ℂ) ^ 2 *
        eigenval (fun g => (Real.exp (b * ((Matrix.trace (repM G g)).re / dim G)) : ℂ))
          (F i).τ = (Fintype.card (F i).κ : ℂ) *
        ∫ g, (Real.exp (b * ((Matrix.trace (repM G g)).re / dim G)) : ℂ) *
          starRingEnd ℂ (Matrix.trace ((F i).τ g)) ∂probHaar G := by
      simp only [eigenval, hinv]
      field_simp
    rw [heig, show (fun n => (c n : ℂ) * ((Fintype.card (F i).κ : ℂ) * mom n (F i))) =
      fun n => (Fintype.card (F i).κ : ℂ) * ((c n : ℂ) * mom n (F i)) from
        funext fun n => by ring]
    exact (hI i).mul_left _
  -- the double series over `ℕ × I`
  obtain ⟨f, hf⟩ : ∃ f : ℕ × I → ℂ, ∀ n i,
      f (n, i) = (c n : ℂ) * ((Fintype.card (F i).κ : ℂ) * mom n (F i)) :=
    ⟨fun p => (c p.1 : ℂ) * ((Fintype.card (F p.2).κ : ℂ) * mom p.1 (F p.2)), fun n i => rfl⟩
  have hnorm : ∀ n i, ‖(Fintype.card (F i).κ : ℂ) * mom n (F i)‖ =
      ((Fintype.card (F i).κ : ℂ) * mom n (F i)).re := fun n i => by
    obtain ⟨m, hm⟩ := exists_mom_eq n (F i)
    rw [hm, ← Nat.cast_mul, Complex.norm_natCast, Complex.natCast_re]
  have hrow : ∀ n, HasSum (fun i => ‖f (n, i)‖) (|c n| * (2 * (dim G : ℝ)) ^ n) := fun n => by
    have h := ((Complex.hasSum_iff _ _).mp (hasSum_dim_mom n F hF)).1
    simp only [← hnorm, Complex.natCast_re] at h
    rw [show (fun i => ‖f (n, i)‖) =
        fun i => |c n| * ‖(Fintype.card (F i).κ : ℂ) * mom n (F i)‖ from funext fun i => by
          rw [hf n i, norm_mul, Complex.norm_real, Real.norm_eq_abs],
      show |c n| * (2 * (dim G : ℝ)) ^ n = |c n| * (((2 * dim G) ^ n : ℕ) : ℝ) by push_cast; ring]
    exact h.mul_left _
  have hS : Summable f := by
    refine Summable.of_norm ((summable_prod_of_nonneg fun p => norm_nonneg (f p)).mpr
      ⟨fun n => (hrow n).summable, hsum.congr fun n => ?_⟩)
    exact ((hrow n).tsum_eq).symm
  have htot : HasSum (fun n => (c n : ℂ) * (((2 * dim G) ^ n : ℕ) : ℂ)) (Real.exp b : ℂ) := by
    have h2 : (2 * (dim G : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr dim_pos.ne')
    rw [show (fun n => (c n : ℂ) * (((2 * dim G) ^ n : ℕ) : ℂ)) =
      fun n => ((b ^ n / n.factorial : ℝ) : ℂ) from funext fun n => by
        rw [hc n]
        push_cast
        rw [div_mul_eq_mul_div, ← mul_pow, div_mul_cancel₀ _ h2]]
    exact Complex.hasSum_ofReal.mpr (CharacterExpansion.hasSum_exp_div b)
  have h1 : HasSum (fun n => (c n : ℂ) * (((2 * dim G) ^ n : ℕ) : ℂ)) (∑' p, f p) :=
    hS.hasSum.prod_fiberwise fun n => by
      simp_rw [hf]
      exact (hasSum_dim_mom n F hF).mul_left _
  have h2 := ((Equiv.prodComm I ℕ).hasSum_iff.mpr hS.hasSum).prod_fiberwise fun i => by
    show HasSum (fun n => f (n, i)) _
    simp_rw [hf]
    exact hfibI i
  rwa [h1.unique htot] at h2

#print axioms exists_tensorPow
#print axioms exists_mom_eq
#print axioms hasSum_dim_mom
#print axioms hasSum_dim_sq_eigenval

end MassGap.PurityKernelSeries
