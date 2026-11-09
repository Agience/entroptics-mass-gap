import Mathlib
import MassGap.CompositesBuild

/-!
# MassGap.ClassicalLimit — classical leading terms of the lattice composites

For a smooth admissible potential `A` and a coupling `g`, the classical configuration
`U_μ(x) = exp(i a g A_μ(a x))` (`IsClassCfg`) is read by gauge-covariant lattice letters at the
origin:

* `latD U ρ σ [] x = U_p(x) − 1`, `U_p` the plaquette holonomy
  `U_ρ(x) U_σ(x+ρ̂) U_ρ(x+σ̂)⁻¹ U_σ(x)⁻¹`;
* `latD U ρ σ (μ :: ds) x = U_μ(x) · latD U ρ σ ds (x+μ̂) · U_μ(x)⁻¹ − latD U ρ σ ds x`, the
  parallel-transported finite difference.

A word `W` of letters is read as `latW U W`, the product of its letters at the origin; a classical
monomial `m` as `monoV m U = ∏_{(W,b) ∈ m} Re/Im ((−i)^{|W|} tr (latW U W))` (`bareF m`, a local
gauge-invariant lattice field).

## The theorems

* `ord_covDF`: on the classical configurations, the letter `latD · ρ σ ds` equals
  `a^{|ds|+2} • G(a, a x)` with `G` jointly smooth in `(a, z)` and
  `G(0, z) = (i g) • D_{ds} F_{ρσ}(z)`. The proof is by Hadamard's lemma (`hadamard`, built on
  `contDiff_integral01`, smoothness of `x ↦ ∫₀¹ F(x, t) dt`): the plaquette factors as
  `(U_ρ U_σ' − U_σ U_ρ') U_ρ'⁻¹ U_σ⁻¹`, each link is `1 + a L` with `L(0) = i g A`, and each lattice
  translation by `a v` is `a • S` with `S(0) = ∂_v`.
* `classicalLead_bareF`: for every monomial `m ≠ []` whose words are non-empty,
  `ClassicalLead (bareF m).1 (cdim m) (fun A g => g ^ cnF m * cval g A m)`.
* `tiedB_bareF`: `CompositesBuild.TiedB (fun i => bareF i.1)`.
* `classicalLead_ffT`: the field `bareF (emono β) = −Re tr(latD β₀β₁ · latD β₂β₃)` has classical
  leading term `g² ffT g A β` at dimension `4`.
* `classicalLead_sum`: `ClassicalLead` is closed under finite real combinations.
* `ffMix`, `ffMix_lead`: the mixing whose basis is `bareF (emono β)`, with `Mb = 1`, satisfies the
  third clause of `ChannelTie` for every `β`. `channelTie_ffMixZ` gives the whole `ChannelTie` for
  every hypercubic-equivariant `Z` (mixing `M k = Z k`), `channelTie_ffMix` at a scalar
  `Z k = z k • 1`. These prove `ChannelTie` in isolation: `ffMix` is not usable as the shared mixing
  of `ScalarTie`, `TopNorm` or `SepConv`, since its trace channel `∑ −Re tr((U_{μν} − 1)²)` is not a
  multiple of `sym (plaqField q0)`.
* `ffMixS`, `channelTie_ffMixS`: the basis `Idx4 ⊕ Unit`, the tensor fields `bareF (emono β)` and
  `sym (plaqField q0)`, with the same `ChannelTie` for every hypercubic-equivariant `Z`. That
  `sym (plaqField q0)` lies in the basis is what `ScalarTie` reads; `ScalarTie` itself is not proved
  here.
* The bare fields use forward plaquettes based at the origin: their corrections are `O(a)` relative,
  and the bare field `bareF (emono β)` has no hypercubic symmetry of its own.

DERIVED (module-wide): `4` the dimension and the dimension of `tr F F`; `2` the dimension of a
plaquette letter and the power of `g` in `tr F F`; `0` the origin and `a = 0`; `1` the unit matrix
and the unit interval.
-/

noncomputable section

namespace MassGap.ClassicalLimit

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ClayStatement Filter
open scoped Topology Matrix ContDiff

/-! ## 1. Hadamard's lemma with parameters -/

section Hadamard

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup M] [NormedSpace ℝ M] [CompleteSpace M]

/-- Differentiation of `x ↦ ∫₀¹ F(x, t) dt` under the integral. DERIVED: `0`, `1` the interval. -/
theorem hasFDerivAt_integral01 {F : E × ℝ → M} (hF : ContDiff ℝ 1 F) (x : E) :
    HasFDerivAt (fun y => ∫ t in (0:ℝ)..1, F (y, t))
      (∫ t in (0:ℝ)..1, (fderiv ℝ F (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  have hc : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  have hFc : Continuous F := hF.continuous
  have hF'c : Continuous (fun p : E × ℝ =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)) :=
    hc.clm_comp continuous_const
  have hK : IsCompact (Metric.closedBall x 1 ×ˢ Set.Icc (0:ℝ) 1) :=
    (isCompact_closedBall x 1).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'c.continuousOn
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (s := Metric.ball x 1) (bound := fun _ => C)
    (F' := fun y t => (fderiv ℝ F (y, t)).comp (ContinuousLinearMap.inl ℝ E ℝ))
    (Metric.ball_mem_nhds x one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · exact Eventually.of_forall fun y =>
      (hFc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hFc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  · exact (hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · refine MeasureTheory.ae_of_all _ fun t ht y hy => hC (y, t) ⟨?_, ?_⟩
    · exact Metric.ball_subset_closedBall hy
    · rw [Set.uIoc_of_le zero_le_one] at ht
      exact Set.Ioc_subset_Icc_self ht
  · refine MeasureTheory.ae_of_all _ fun t _ y _ => ?_
    exact ((hF.differentiable one_ne_zero) (y, t)).hasFDerivAt.comp y
      (hasFDerivAt_prodMk_left y t)

/-- **Smoothness of a parametric integral** over `[0, 1]`.

DERIVED: `0`, `1` the interval. -/
theorem contDiff_integral01 {F : E × ℝ → M} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun y => ∫ t in (0:ℝ)..1, F (y, t)) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing F with
  | zero =>
    exact contDiff_zero.2
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun y t => F (y, t)) hF.continuous 0 1)
  | succ n ih =>
    have hF1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast le_top)
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun x => (hasFDerivAt_integral01 hF1 x).differentiableAt,
      fun h => absurd h (by simp), fun v => ?_⟩
    have hD : ContDiff ℝ ∞ (fderiv ℝ F) := (contDiff_infty_iff_fderiv.1 hF).2
    have heq : (fun x => fderiv ℝ (fun y => ∫ t in (0:ℝ)..1, F (y, t)) x v) =
        fun x => ∫ t in (0:ℝ)..1, fderiv ℝ F (x, t) (v, 0) := by
      funext x
      rw [(hasFDerivAt_integral01 hF1 x).fderiv, ContinuousLinearMap.intervalIntegral_apply]
      · rfl
      · exact ((hD.continuous.clm_comp continuous_const).comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
    rw [heq]
    exact ih (F := fun p => fderiv ℝ F p (v, 0)) (hD.clm_apply contDiff_const)

/-- **Hadamard's lemma with parameters**: a smooth `K(a, z)` vanishing at `a = 0` is `a • H(a, z)`
with `H` smooth and `H(0, z) = ∂_a K(0, z)`.

DERIVED: `0` the point `a = 0`; `1`, `0` the direction `∂_a`. -/
theorem hadamard {K : ℝ × E → M} (hK : ContDiff ℝ ∞ K) (h0 : ∀ z, K (0, z) = 0) :
    ∃ H : ℝ × E → M, ContDiff ℝ ∞ H ∧ (∀ a z, K (a, z) = a • H (a, z)) ∧
      ∀ z, H (0, z) = fderiv ℝ K (0, z) (1, 0) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ K) := (contDiff_infty_iff_fderiv.1 hK).2
  refine ⟨fun p => ∫ t in (0:ℝ)..1, fderiv ℝ K (t * p.1, p.2) (1, 0), ?_, ?_, ?_⟩
  · exact contDiff_integral01 (E := ℝ × E)
      (F := fun q : (ℝ × E) × ℝ => fderiv ℝ K (q.2 * q.1.1, q.1.2) (1, 0))
      ((hD.comp ((contDiff_snd.mul (contDiff_fst.comp contDiff_fst)).prodMk
        (contDiff_snd.comp contDiff_fst))).clm_apply contDiff_const)
  · intro a z
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (fun s : ℝ => K (s * a, z)) (a • fderiv ℝ K (t * a, z) (1, 0)) t := by
      intro t _
      have h1 : HasDerivAt (fun s : ℝ => ((s * a, z) : ℝ × E)) ((a, 0) : ℝ × E) t := by
        have := ((hasDerivAt_id' t).mul_const a).prodMk (hasDerivAt_const t z)
        simpa using this
      have h2 := ((hK.differentiable (by simp)) (t * a, z)).hasFDerivAt.comp_hasDerivAt t h1
      have h3 : ((a, 0) : ℝ × E) = a • ((1, 0) : ℝ × E) := by simp
      rw [h3, map_smul] at h2
      exact h2
    have hint : IntervalIntegrable (fun t => a • fderiv ℝ K (t * a, z) (1, 0))
        MeasureTheory.volume 0 1 :=
      (((hD.continuous.comp ((continuous_id.mul continuous_const).prodMk continuous_const)).clm_apply
        continuous_const).const_smul a).intervalIntegrable 0 1
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simp only [one_mul, zero_mul, h0, sub_zero] at this
    rw [← this, intervalIntegral.integral_smul]
  · intro z
    simp [intervalIntegral.integral_const]

end Hadamard

/-! ## 2. The lattice letters -/

/-- The matrix type. DERIVED: no numeral. -/
abbrev Mat (N : ℕ) : Type := Matrix (Fin N) (Fin N) ℂ

/-- The parameter space `(a, z)`: spacing and base point. DERIVED: `4` the dimension. -/
abbrev Par : Type := ℝ × (Fin 4 → ℝ)

variable {N : ℕ}

section Lattice

/-- The link matrix. DERIVED: no numeral. -/
def lk (U : Cfg N) (l : ILink) : Mat N := ((U l : MassGap.SUN.SU N) : Mat N)

/-- The inverse link matrix. DERIVED: no numeral. -/
def lki (U : Cfg N) (l : ILink) : Mat N := (((U l)⁻¹ : MassGap.SUN.SU N) : Mat N)

/-- The plaquette holonomy `U_ρ(x) U_σ(x+ρ̂) U_ρ(x+σ̂)⁻¹ U_σ(x)⁻¹` in the group.

DERIVED: `4` the dimension. -/
def plaqG (U : Cfg N) (ρ σ : Fin 4) (x : ISite) : MassGap.SUN.SU N :=
  U (ρ, x) * U (σ, ishift ρ x) * (U (ρ, ishift σ x))⁻¹ * (U (σ, x))⁻¹

/-- **The lattice letter** `D_{ds} F_{ρσ}` at site `x`: `U_p − 1`, then parallel-transported
differences. DERIVED: `1` the unit matrix; `4` the dimension. -/
def latD (U : Cfg N) (ρ σ : Fin 4) : List (Fin 4) → ISite → Mat N
  | [] => fun x => ((plaqG U ρ σ x : MassGap.SUN.SU N) : Mat N) - 1
  | μ :: ds => fun x =>
      lk U (μ, x) * latD U ρ σ ds (ishift μ x) * lki U (μ, x) - latD U ρ σ ds x

/-- The lattice word at the origin. DERIVED: `0` the origin. -/
def latW (U : Cfg N) (W : Word) : Mat N := (W.map fun l => latD U l.2.1 l.2.2 l.1 0).prod

/-- The lattice factor `Re/Im ((−i)^{|W|} tr W)`. DERIVED: no numeral. -/
def facV (U : Cfg N) (p : Word × Bool) : ℝ :=
  if p.2 then ((-Complex.I) ^ p.1.length * Matrix.trace (latW U p.1)).re
  else ((-Complex.I) ^ p.1.length * Matrix.trace (latW U p.1)).im

/-- The lattice monomial. DERIVED: no numeral. -/
def monoV (m : CMono) (U : Cfg N) : ℝ := (m.map fun p => facV U p).prod

theorem latW_cons (U : Cfg N) (l : Letter) (W : Word) :
    latW U (l :: W) = latD U l.2.1 l.2.2 l.1 0 * latW U W := rfl

theorem monoV_cons (p : Word × Bool) (m : CMono) (U : Cfg N) :
    monoV (p :: m) U = facV U p * monoV m U := rfl

/-! ### Continuity -/

theorem continuous_lk (l : ILink) : Continuous fun U : Cfg N => lk U l :=
  continuous_subtype_val.comp (continuous_apply l)

theorem continuous_lki (l : ILink) : Continuous fun U : Cfg N => lki U l :=
  continuous_subtype_val.comp (continuous_apply l).inv

theorem continuous_plaqG (ρ σ : Fin 4) (x : ISite) :
    Continuous fun U : Cfg N => ((plaqG U ρ σ x : MassGap.SUN.SU N) : Mat N) := by
  have h1 : Continuous fun U : Cfg N => U (ρ, x) := continuous_apply _
  have h2 : Continuous fun U : Cfg N => U (σ, ishift ρ x) := continuous_apply _
  have h3 : Continuous fun U : Cfg N => U (ρ, ishift σ x) := continuous_apply _
  have h4 : Continuous fun U : Cfg N => U (σ, x) := continuous_apply _
  exact continuous_subtype_val.comp (((h1.mul h2).mul h3.inv).mul h4.inv)

theorem continuous_latD (ρ σ : Fin 4) :
    ∀ (ds : List (Fin 4)) (x : ISite), Continuous fun U : Cfg N => latD U ρ σ ds x
  | [], x => (continuous_plaqG ρ σ x).sub continuous_const
  | μ :: ds, x =>
    (((continuous_lk _).mul (continuous_latD ρ σ ds _)).mul (continuous_lki _)).sub
      (continuous_latD ρ σ ds x)

theorem continuous_latW : ∀ W : Word, Continuous fun U : Cfg N => latW U W
  | [] => by
    have : (fun U : Cfg N => latW U []) = fun _ => 1 := rfl
    rw [this]; exact continuous_const
  | l :: W => by
    simp only [latW, List.map_cons, List.prod_cons]
    exact (continuous_latD _ _ _ _).mul (continuous_latW W)

theorem continuous_facV (p : Word × Bool) : Continuous fun U : Cfg N => facV U p := by
  obtain ⟨W, b⟩ := p
  have h : Continuous fun U : Cfg N =>
      (-Complex.I) ^ W.length * Matrix.trace (latW U W) :=
    continuous_const.mul (continuous_latW W).matrix_trace
  cases b
  · exact Complex.continuous_im.comp h
  · exact Complex.continuous_re.comp h

theorem continuous_monoV : ∀ m : CMono, Continuous (monoV (N := N) m)
  | [] => by
    have : monoV (N := N) [] = fun _ => 1 := rfl
    rw [this]; exact continuous_const
  | p :: m => by
    have : monoV (N := N) (p :: m) = fun U => facV U p * monoV m U := rfl
    rw [this]
    exact (continuous_facV p).mul (continuous_monoV m)

/-! ### Locality -/

/-- The links a letter reads. DERIVED: `4` the dimension. -/
def linksD (ρ σ : Fin 4) : List (Fin 4) → ISite → Finset ILink
  | [] => fun x => {(ρ, x), (σ, ishift ρ x), (ρ, ishift σ x), (σ, x)}
  | μ :: ds => fun x => insert (μ, x) (linksD ρ σ ds (ishift μ x) ∪ linksD ρ σ ds x)

/-- The links a word reads. DERIVED: `0` the origin. -/
def linksW : Word → Finset ILink
  | [] => ∅
  | l :: W => linksD l.2.1 l.2.2 l.1 0 ∪ linksW W

/-- The links a monomial reads. DERIVED: no numeral. -/
def linksM : CMono → Finset ILink
  | [] => ∅
  | p :: m => linksW p.1 ∪ linksM m

theorem latD_local (ρ σ : Fin 4) :
    ∀ (ds : List (Fin 4)) (x : ISite) (U V : Cfg N), (∀ l ∈ linksD ρ σ ds x, U l = V l) →
      latD U ρ σ ds x = latD V ρ σ ds x
  | [], x, U, V, h => by
    have h1 := h (ρ, x) (by simp [linksD])
    have h2 := h (σ, ishift ρ x) (by simp [linksD])
    have h3 := h (ρ, ishift σ x) (by simp [linksD])
    have h4 := h (σ, x) (by simp [linksD])
    simp only [latD, plaqG, h1, h2, h3, h4]
  | μ :: ds, x, U, V, h => by
    have h0 := h (μ, x) (by simp [linksD])
    have ha := latD_local ρ σ ds (ishift μ x) U V
      (fun l hl => h l (by simp [linksD, hl]))
    have hb := latD_local ρ σ ds x U V (fun l hl => h l (by simp [linksD, hl]))
    simp only [latD, lk, lki, h0, ha, hb]

theorem latW_local : ∀ (W : Word) (U V : Cfg N), (∀ l ∈ linksW W, U l = V l) →
    latW U W = latW V W
  | [], _, _, _ => by simp [latW]
  | l :: W, U, V, h => by
    rw [latW_cons, latW_cons,
      latD_local l.2.1 l.2.2 l.1 0 U V (fun k hk => h k (by simp [linksW, hk])),
      latW_local W U V (fun k hk => h k (by simp [linksW, hk]))]

theorem monoV_local : ∀ m : CMono, IsLocalOn (linksM m) (monoV (N := N) m)
  | [] => fun _ _ _ => by simp [monoV]
  | p :: m => fun U V h => by
    have hp : facV U p = facV V p := by
      unfold facV
      rw [latW_local p.1 U V (fun k hk => h k (by simp [linksM, hk]))]
    rw [monoV_cons, monoV_cons, hp, monoV_local m U V (fun k hk => h k (by simp [linksM, hk]))]

/-! ### Gauge covariance -/

theorem coe_mulSU (h k : MassGap.SUN.SU N) : ((h * k : MassGap.SUN.SU N) : Mat N) = h * k := rfl

theorem coe_oneSU : ((1 : MassGap.SUN.SU N) : Mat N) = 1 := rfl

theorem coe_inv_mul (h : MassGap.SUN.SU N) : ((h⁻¹ : MassGap.SUN.SU N) : Mat N) * h = 1 := by
  rw [← coe_mulSU, inv_mul_cancel, coe_oneSU]

theorem coe_mul_inv (h : MassGap.SUN.SU N) : (h : Mat N) * ((h⁻¹ : MassGap.SUN.SU N) : Mat N) = 1 := by
  rw [← coe_mulSU, mul_inv_cancel, coe_oneSU]

theorem plaqG_gauge (g : ISite → MassGap.SUN.SU N) (U : Cfg N) (ρ σ : Fin 4) (x : ISite) :
    plaqG (GaugeInvariantAlgebra.igaugeTransform g U) ρ σ x = g x * plaqG U ρ σ x * (g x)⁻¹ := by
  simp only [plaqG, GaugeInvariantAlgebra.igaugeTransform]
  rw [MassGap.InfiniteShift.ishift_comm ρ σ x]
  group

theorem latD_gauge (g : ISite → MassGap.SUN.SU N) (U : Cfg N) (ρ σ : Fin 4) :
    ∀ (ds : List (Fin 4)) (x : ISite),
      latD (GaugeInvariantAlgebra.igaugeTransform g U) ρ σ ds x
        = (g x : Mat N) * latD U ρ σ ds x * ((g x)⁻¹ : MassGap.SUN.SU N)
  | [], x => by
    simp only [latD]
    rw [plaqG_gauge, coe_mulSU, coe_mulSU, mul_sub, sub_mul, mul_one, coe_mul_inv]
  | μ :: ds, x => by
    simp only [latD]
    rw [latD_gauge g U ρ σ ds (ishift μ x), latD_gauge g U ρ σ ds x]
    have hl : lk (GaugeInvariantAlgebra.igaugeTransform g U) (μ, x)
        = (g x : Mat N) * lk U (μ, x) * ((g (ishift μ x))⁻¹ : MassGap.SUN.SU N) := rfl
    have hli : lki (GaugeInvariantAlgebra.igaugeTransform g U) (μ, x)
        = (g (ishift μ x) : Mat N) * lki U (μ, x) * ((g x)⁻¹ : MassGap.SUN.SU N) := by
      simp only [lki, GaugeInvariantAlgebra.igaugeTransform, mul_inv_rev, inv_inv]
      simp only [coe_mulSU, mul_assoc]
    rw [hl, hli]
    have hy : ∀ X : Mat N, ((g (ishift μ x))⁻¹ : MassGap.SUN.SU N) * ((g (ishift μ x) : Mat N) * X) = X :=
      fun X => by rw [← mul_assoc, coe_inv_mul, one_mul]
    simp only [mul_assoc, hy, mul_sub, sub_mul]

theorem latW_gauge (g : ISite → MassGap.SUN.SU N) (U : Cfg N) :
    ∀ W : Word, latW (GaugeInvariantAlgebra.igaugeTransform g U) W
      = (g 0 : Mat N) * latW U W * ((g 0)⁻¹ : MassGap.SUN.SU N)
  | [] => by simp only [latW, List.map_nil, List.prod_nil, mul_one, coe_mul_inv]
  | l :: W => by
    rw [latW_cons, latW_cons, latD_gauge, latW_gauge g U W]
    have hy : ∀ X : Mat N, ((g 0)⁻¹ : MassGap.SUN.SU N) * ((g 0 : Mat N) * X) = X :=
      fun X => by rw [← mul_assoc, coe_inv_mul, one_mul]
    simp only [mul_assoc, hy]

theorem trace_latW_gauge (g : ISite → MassGap.SUN.SU N) (U : Cfg N) (W : Word) :
    Matrix.trace (latW (GaugeInvariantAlgebra.igaugeTransform g U) W) = Matrix.trace (latW U W) := by
  rw [latW_gauge, Matrix.trace_mul_comm, ← mul_assoc, coe_inv_mul, one_mul]

theorem monoV_gauge (g : ISite → MassGap.SUN.SU N) (U : Cfg N) :
    ∀ m : CMono, monoV m (GaugeInvariantAlgebra.igaugeTransform g U) = monoV m U
  | [] => by simp [monoV]
  | p :: m => by
    have hp : facV (GaugeInvariantAlgebra.igaugeTransform g U) p = facV U p := by
      unfold facV; rw [trace_latW_gauge]
    rw [monoV_cons, monoV_cons, hp, monoV_gauge g U m]

/-- **The bare lattice field of a classical monomial**: continuous, local on `linksM m`, gauge
invariant. DERIVED: no numeral. -/
def bareF (m : CMono) : LField (MassGap.SUN.SU N) :=
  ⟨⟨monoV m, continuous_monoV m⟩, ⟨⟨linksM m, monoV_local m⟩, fun g U => monoV_gauge g U m⟩⟩

theorem bareF_apply (m : CMono) (U : Cfg N) : (bareF m).1 U = monoV m U := rfl

/-! ### The unit configuration -/

theorem latD_one (ρ σ : Fin 4) :
    ∀ (ds : List (Fin 4)) (x : ISite), latD (fun _ => (1 : MassGap.SUN.SU N)) ρ σ ds x = 0
  | [], x => by simp only [latD, plaqG, inv_one, mul_one, coe_oneSU, sub_self]
  | μ :: ds, x => by
    simp only [latD, latD_one ρ σ ds, mul_zero, zero_mul, sub_self]

theorem monoV_one {m : CMono} (hm : m ≠ []) (hw : ∀ p ∈ m, p.1 ≠ []) :
    monoV m (fun _ => (1 : MassGap.SUN.SU N)) = 0 := by
  obtain ⟨p, m', rfl⟩ := List.exists_cons_of_ne_nil hm
  obtain ⟨l, W, hW⟩ := List.exists_cons_of_ne_nil (hw p (by simp))
  have hf : facV (fun _ => (1 : MassGap.SUN.SU N)) p = 0 := by
    unfold facV
    rw [hW]
    simp only [latW, List.map_cons, List.prod_cons, latD_one, zero_mul, Matrix.trace_zero,
      mul_zero, Complex.zero_re, Complex.zero_im, ite_self]
  simp only [monoV, List.map_cons, List.prod_cons, hf, zero_mul]

/-! ### The continuum letters -/

/-- The continuum link `exp(a s A_μ(z))` at `p = (a, z)`. DERIVED: no numeral. -/
def ex (A : GPot N) (s : ℂ) (μ : Fin 4) (p : Par) : Mat N :=
  NormedSpace.exp (p.1 • (s • Matrix.of (A p.2 μ)))

/-- The translation `(a, z) ↦ (a, z + a v)`. DERIVED: no numeral. -/
def shf (v : Fin 4 → ℝ) (p : Par) : Par := (p.1, p.2 + p.1 • v)

/-- **The continuum letter**: the lattice letter on the classical configuration, as a function of
`(a, z)`. DERIVED: `1` the unit matrix; `4` the dimension. -/
def phiD (g : ℝ) (A : GPot N) (ρ σ : Fin 4) : List (Fin 4) → Par → Mat N
  | [] => fun p =>
      ex A (Complex.I * g) ρ p * ex A (Complex.I * g) σ (shf (dir ρ) p)
        * ex A (-(Complex.I * g)) ρ (shf (dir σ) p) * ex A (-(Complex.I * g)) σ p - 1
  | μ :: ds => fun p =>
      ex A (Complex.I * g) μ p * phiD g A ρ σ ds (shf (dir μ) p) * ex A (-(Complex.I * g)) μ p
        - phiD g A ρ σ ds p

set_option backward.isDefEq.respectTransparency false in
theorem ex_mul_neg (A : GPot N) (s : ℂ) (μ : Fin 4) (p : Par) :
    ex A s μ p * ex A (-s) μ p = 1 := by
  unfold ex
  have h : p.1 • ((-s) • Matrix.of (A p.2 μ)) = -(p.1 • (s • Matrix.of (A p.2 μ))) := by
    rw [neg_smul, smul_neg]
  rw [h, ← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl _)), add_neg_cancel,
    NormedSpace.exp_zero]

theorem ex_neg_mul (A : GPot N) (s : ℂ) (μ : Fin 4) (p : Par) :
    ex A (-s) μ p * ex A s μ p = 1 := by
  have := ex_mul_neg A (-s) μ p
  rwa [neg_neg] at this

theorem site_ishift (a : ℝ) (μ : Fin 4) (x : ISite) :
    site a (ishift μ x) = site a x + a • dir μ := by
  funext i
  by_cases h : i = μ
  · subst h; simp [site, ishift, dir, mul_add]
  · simp [site, ishift, dir, Function.update_apply, h, Pi.single_apply]

theorem of_classCfg (a g : ℝ) (A : GPot N) (μ : Fin 4) (y : Fin 4 → ℝ) :
    Matrix.of ((Complex.I * ((a * g : ℝ) : ℂ)) • A y μ)
      = a • ((Complex.I * (g : ℂ)) • Matrix.of (A y μ)) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast; ring

theorem lk_classCfg {a g : ℝ} {A : GPot N} {U : Cfg N} (hU : IsClassCfg a g A U) (μ : Fin 4)
    (x : ISite) : lk U (μ, x) = ex A (Complex.I * g) μ (a, site a x) := by
  simp only [lk, ex, hU (μ, x), of_classCfg]

theorem lki_classCfg {a g : ℝ} {A : GPot N} {U : Cfg N} (hU : IsClassCfg a g A U) (μ : Fin 4)
    (x : ISite) : lki U (μ, x) = ex A (-(Complex.I * g)) μ (a, site a x) := by
  have h1 : lki U (μ, x) * lk U (μ, x) = 1 := coe_inv_mul _
  have h2 : lk U (μ, x) * ex A (-(Complex.I * g)) μ (a, site a x) = 1 := by
    rw [lk_classCfg hU, ex_mul_neg]
  calc lki U (μ, x) = lki U (μ, x) * (lk U (μ, x) * ex A (-(Complex.I * g)) μ (a, site a x)) := by
        rw [h2, mul_one]
    _ = _ := by rw [← mul_assoc, h1, one_mul]

/-- **The lattice letter on a classical configuration is the continuum letter** at `(a, a x)`.

DERIVED: no numeral. -/
theorem latD_classCfg {a g : ℝ} {A : GPot N} {U : Cfg N} (hU : IsClassCfg a g A U) (ρ σ : Fin 4) :
    ∀ (ds : List (Fin 4)) (x : ISite), latD U ρ σ ds x = phiD g A ρ σ ds (a, site a x)
  | [], x => by
    simp only [latD, phiD, plaqG, coe_mulSU]
    rw [show ((U (ρ, x) : MassGap.SUN.SU N) : Mat N) = lk U (ρ, x) from rfl,
      show ((U (σ, ishift ρ x) : MassGap.SUN.SU N) : Mat N) = lk U (σ, ishift ρ x) from rfl,
      show (((U (ρ, ishift σ x))⁻¹ : MassGap.SUN.SU N) : Mat N) = lki U (ρ, ishift σ x) from rfl,
      show (((U (σ, x))⁻¹ : MassGap.SUN.SU N) : Mat N) = lki U (σ, x) from rfl,
      lk_classCfg hU, lk_classCfg hU, lki_classCfg hU, lki_classCfg hU, site_ishift,
      site_ishift] <;> rfl
  | μ :: ds, x => by
    simp only [latD, phiD]
    rw [lk_classCfg hU, lki_classCfg hU, latD_classCfg hU ρ σ ds, latD_classCfg hU ρ σ ds,
      site_ishift] <;> rfl

end Lattice

/-! ## 3. Expansion of the continuum letters -/

section Analysis

open scoped Matrix.Norms.Operator

theorem completeMat : CompleteSpace (Mat N) := FiniteDimensional.complete ℝ (Mat N)

attribute [local instance] completeMat

/-- `Matrix.of` as a continuous linear equivalence. DERIVED: no numeral. -/
def ofL : (Fin N → Fin N → ℂ) ≃L[ℝ] Mat N :=
  LinearEquiv.toContinuousLinearEquiv (Matrix.ofLinearEquiv ℝ)

theorem ofL_apply (X : Fin N → Fin N → ℂ) : ofL X = Matrix.of X := rfl

theorem contDiff_expM : ContDiff ℝ ∞ (fun X : Mat N => NormedSpace.exp X) :=
  AnalyticOnNhd.contDiff fun X _ => NormedSpace.exp_analytic (𝕂 := ℝ) X

theorem contDiff_ofA {A : GPot N} (hA : ContDiff ℝ ∞ A) (μ : Fin 4) :
    ContDiff ℝ ∞ (fun y => Matrix.of (A y μ) : (Fin 4 → ℝ) → Mat N) := by
  have h := (ofL (N := N)).contDiff.comp (n := ∞) (contDiff_pi.1 hA μ)
  exact h

theorem contDiff_ex {A : GPot N} (hA : ContDiff ℝ ∞ A) (s : ℂ) (μ : Fin 4) :
    ContDiff ℝ ∞ (ex A s μ) :=
  contDiff_expM.comp (contDiff_fst.smul (((contDiff_ofA hA μ).comp contDiff_snd).const_smul s))

theorem contDiff_shf (v : Fin 4 → ℝ) : ContDiff ℝ ∞ (shf v) :=
  contDiff_fst.prodMk (contDiff_snd.add (contDiff_fst.smul contDiff_const))

/-- The derivative along `a` at `a = 0`, read off a line derivative. DERIVED: `0`, `1` the line. -/
theorem fderiv_line {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] {G : Par → M}
    {z : Fin 4 → ℝ} (hG : DifferentiableAt ℝ G (0, z)) {D : M}
    (h : HasDerivAt (fun a : ℝ => G (a, z)) D 0) : fderiv ℝ G (0, z) (1, 0) = D := by
  have h1 : HasDerivAt (fun a : ℝ => ((a, z) : Par)) ((1, 0) : Par) 0 :=
    (hasDerivAt_id' 0).prodMk (hasDerivAt_const 0 z)
  exact (hG.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1).unique h

/-- **A lattice translation is `a • S`**: `G(a, z + a v) − G(a, z) = a • S(a, z)` with
`S(0, z) = ∂_v G(0, ·)(z)`. DERIVED: `0` the point `a = 0`. -/
theorem shift_ord {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [CompleteSpace M]
    {G : Par → M} (hG : ContDiff ℝ ∞ G) (v : Fin 4 → ℝ) :
    ∃ S : Par → M, ContDiff ℝ ∞ S ∧ (∀ p, G (shf v p) - G p = p.1 • S p) ∧
      ∀ z, S (0, z) = fderiv ℝ (fun y => G (0, y)) z v := by
  have hK : ContDiff ℝ ∞ (fun p => G (shf v p) - G p) := (hG.comp (contDiff_shf v)).sub hG
  obtain ⟨H, hH, hKH, hH0⟩ := hadamard hK (fun z => by simp [shf])
  refine ⟨H, hH, fun p => hKH p.1 p.2, fun z => ?_⟩
  rw [hH0]
  have hGd : ∀ q, HasFDerivAt G (fderiv ℝ G q) q :=
    fun q => ((hG.differentiable (by simp)) q).hasFDerivAt
  have hline : HasDerivAt (fun a : ℝ => G (shf v (a, z)) - G (a, z))
      (fderiv ℝ G (0, z) (1, v) - fderiv ℝ G (0, z) (1, 0)) 0 := by
    have h1 : HasDerivAt (fun a : ℝ => shf v (a, z)) ((1, v) : Par) 0 := by
      have := (hasDerivAt_id' (0:ℝ)).prodMk
        (((hasDerivAt_id' (0:ℝ)).smul_const v).const_add z)
      simpa [shf] using this
    have h2 : HasDerivAt (fun a : ℝ => ((a, z) : Par)) ((1, 0) : Par) 0 :=
      (hasDerivAt_id' 0).prodMk (hasDerivAt_const 0 z)
    exact ((hGd _).comp_hasDerivAt_of_eq 0 h1 (by simp [shf])).sub ((hGd _).comp_hasDerivAt 0 h2)
  rw [fderiv_line (hK.differentiable (by simp) _) hline, ← map_sub]
  have h3 : HasFDerivAt (fun y => G (0, y)) ((fderiv ℝ G (0, z)).comp
      (ContinuousLinearMap.inr ℝ ℝ (Fin 4 → ℝ))) z :=
    (hGd _).comp z (hasFDerivAt_prodMk_right 0 z)
  rw [h3.fderiv]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- **A link is `1 + a L`** with `L(0, z) = s A_μ(z)`. DERIVED: `1` the unit matrix. -/
theorem ex_ord {A : GPot N} (hA : ContDiff ℝ ∞ A) (s : ℂ) (μ : Fin 4) :
    ∃ L : Par → Mat N, ContDiff ℝ ∞ L ∧ (∀ p, ex A s μ p = 1 + p.1 • L p) ∧
      ∀ z, L (0, z) = s • Matrix.of (A z μ) := by
  have hK : ContDiff ℝ ∞ (fun p => ex A s μ p - 1) := (contDiff_ex hA s μ).sub contDiff_const
  obtain ⟨H, hH, hKH, hH0⟩ := hadamard hK (fun z => by simp [ex])
  refine ⟨H, hH, fun p => ?_, fun z => ?_⟩
  · have e : ex A s μ p - 1 = p.1 • H p := hKH p.1 p.2
    rw [← e]; abel
  · rw [hH0]
    apply fderiv_line (hK.differentiable (by simp) _)
    have := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (s • (Matrix.of (A z μ) : Mat N)) 0).sub_const 1
    simpa [ex] using this

set_option backward.isDefEq.respectTransparency false in
/-- `∂_v (c • A(·))`. DERIVED: no numeral. -/
theorem fderiv_cof {f : (Fin 4 → ℝ) → Fin N → Fin N → ℂ} {z : Fin 4 → ℝ}
    (hf : DifferentiableAt ℝ f z) (s : ℂ) (v : Fin 4 → ℝ) :
    fderiv ℝ (fun y => s • (Matrix.of (f y) : Mat N)) z v = s • Matrix.of (fderiv ℝ f z v) := by
  have h1 : HasFDerivAt (⇑(ofL (N := N)) ∘ f)
      (((ofL (N := N)) : (Fin N → Fin N → ℂ) →L[ℝ] Mat N).comp (fderiv ℝ f z)) z :=
    ((ofL (N := N)).hasFDerivAt).comp z hf.hasFDerivAt
  simp only [Function.comp_def] at h1
  simp only [ofL_apply] at h1
  have h2 := h1.const_smul s
  rw [show (fun y => s • (Matrix.of (f y) : Mat N)) = s • (fun x => (Matrix.of (f x) : Mat N))
    from rfl, h2.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ofL_apply]

theorem of_mcomm (X Y : Fin N → Fin N → ℂ) :
    (Matrix.of (mcomm X Y) : Mat N) = Matrix.of X * Matrix.of Y - Matrix.of Y * Matrix.of X := by
  simp [mcomm]

/-- The order statement: `Φ(p) = a^k • G(p)`, `G` smooth, `G(0, z) = C z`. DERIVED: `0` `a = 0`. -/
def OrdA (k : ℕ) (Φ : Par → Mat N) (C : (Fin 4 → ℝ) → Mat N) : Prop :=
  ∃ G : Par → Mat N, ContDiff ℝ ∞ G ∧ (∀ p, Φ p = p.1 ^ k • G p) ∧ ∀ z, G (0, z) = C z

set_option backward.isDefEq.respectTransparency false in
/-- **The plaquette letter**: `U_p − 1 = a² G`, `G(0, z) = i g F_{ρσ}(z)`.

DERIVED: `2` the dimension of `F`. -/
theorem ord_base {A : GPot N} (hA : ContDiff ℝ ∞ A) (g : ℝ) (ρ σ : Fin 4) :
    OrdA 2 (phiD g A ρ σ []) (fun z => (Complex.I * g) • Matrix.of (covDF g A ρ σ [] z)) := by
  obtain ⟨Lρ, hLρ, eρ, zρ⟩ := ex_ord hA (Complex.I * g) ρ
  obtain ⟨Lσ, hLσ, eσ, zσ⟩ := ex_ord hA (Complex.I * g) σ
  obtain ⟨Sσ, hSσ, eSσ, zSσ⟩ := shift_ord hLσ (dir ρ)
  obtain ⟨Sρ, hSρ, eSρ, zSρ⟩ := shift_ord hLρ (dir σ)
  refine ⟨fun p => (Sσ p - Sρ p + Lρ p * Lσ (shf (dir ρ) p) - Lσ p * Lρ (shf (dir σ) p))
      * (ex A (-(Complex.I * g)) ρ (shf (dir σ) p) * ex A (-(Complex.I * g)) σ p),
    ?_, fun p => ?_, fun z => ?_⟩
  · exact ((((hSσ.sub hSρ).add (hLρ.mul (hLσ.comp (contDiff_shf _)))).sub
      (hLσ.mul (hLρ.comp (contDiff_shf _)))).mul
      (((contDiff_ex hA _ ρ).comp (contDiff_shf _)).mul (contDiff_ex hA _ σ)))
  · -- the factorisation `U_p − 1 = (V₁V₂ − V₄'V₃') V₃V₄`
    have hfac : phiD g A ρ σ [] p
        = (ex A (Complex.I * g) ρ p * ex A (Complex.I * g) σ (shf (dir ρ) p)
            - ex A (Complex.I * g) σ p * ex A (Complex.I * g) ρ (shf (dir σ) p))
          * (ex A (-(Complex.I * g)) ρ (shf (dir σ) p) * ex A (-(Complex.I * g)) σ p) := by
      simp only [phiD, sub_mul, mul_assoc]
      congr 1
      rw [← mul_assoc (ex A (Complex.I * g) ρ (shf (dir σ) p)), ex_mul_neg, one_mul, ex_mul_neg]
    rw [hfac, ← smul_mul_assoc]
    congr 1
    have h2 : Lσ (shf (dir ρ) p) = Lσ p + p.1 • Sσ p := by rw [← eSσ p]; abel
    have h4 : Lρ (shf (dir σ) p) = Lρ p + p.1 • Sρ p := by rw [← eSρ p]; abel
    have hs : ∀ v, (shf v p).1 = p.1 := fun v => rfl
    rw [eρ p, eσ (shf (dir ρ) p), eσ p, eρ (shf (dir σ) p), hs, hs, h2, h4]
    simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add,
      smul_sub, mul_sub, sub_mul, smul_smul, mul_assoc]
    module
  · have hs0 : ∀ v, shf v ((0 : ℝ), z) = (0, z) := fun v => by simp [shf]
    have hex0 : ∀ s μ, ex A s μ ((0 : ℝ), z) = 1 := fun s μ => by simp [ex]
    simp only []
    rw [hs0, hs0, hex0, hex0, mul_one, zSσ, zSρ, zρ, zσ]
    have hfσ : (fun y => Lσ (0, y)) = fun y => (Complex.I * g) • (Matrix.of (A y σ) : Mat N) :=
      funext zσ
    have hfρ : (fun y => Lρ (0, y)) = fun y => (Complex.I * g) • (Matrix.of (A y ρ) : Mat N) :=
      funext zρ
    have hdA : ∀ ν, Differentiable ℝ (fun y => A y ν) :=
      fun ν => (contDiff_pi.1 hA ν).differentiable (by simp)
    rw [hfσ, hfρ, fderiv_cof (hdA σ z), fderiv_cof (hdA ρ z)]
    simp only [covDF, ← Matrix.of_add_of, ← Matrix.of_sub_of, ← Matrix.smul_of, of_mcomm,
      smul_add, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, mul_one]
    try abel

set_option backward.isDefEq.respectTransparency false in
/-- **The transported difference raises the order by one** and acts as `D_μ`.

DERIVED: `1` the extra power of `a`. -/
theorem ord_step {A : GPot N} (hA : ContDiff ℝ ∞ A) (g : ℝ) (ρ σ μ : Fin 4) (ds : List (Fin 4))
    (k : ℕ) (h : OrdA k (phiD g A ρ σ ds) (fun z => (Complex.I * g) • Matrix.of (covDF g A ρ σ ds z))) :
    OrdA (k + 1) (phiD g A ρ σ (μ :: ds))
      (fun z => (Complex.I * g) • Matrix.of (covDF g A ρ σ (μ :: ds) z)) := by
  obtain ⟨G, hG, eG, zG⟩ := h
  obtain ⟨LV, hLV, eV, zV⟩ := ex_ord hA (Complex.I * g) μ
  obtain ⟨LW, hLW, eW, zW⟩ := ex_ord hA (-(Complex.I * g)) μ
  obtain ⟨S, hS, eS, zS⟩ := shift_ord hG (dir μ)
  refine ⟨fun p => S p + LV p * G (shf (dir μ) p) + G (shf (dir μ) p) * LW p
      + p.1 • (LV p * G (shf (dir μ) p) * LW p), ?_, fun p => ?_, fun z => ?_⟩
  · have hGs := hG.comp (contDiff_shf (dir μ))
    exact ((hS.add (hLV.mul hGs)).add (hGs.mul hLW)).add
      (contDiff_fst.smul ((hLV.mul hGs).mul hLW))
  · simp only [phiD]
    have h1 : G (shf (dir μ) p) = G p + p.1 • S p := by rw [← eS p]; abel
    have hs : (shf (dir μ) p).1 = p.1 := rfl
    rw [eG (shf (dir μ) p), eG p, eV p, eW p, hs, h1]
    simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add,
      smul_sub, mul_sub, sub_mul, smul_smul, mul_assoc, pow_succ]
    module
  · have hs0 : shf (dir μ) ((0 : ℝ), z) = (0, z) := by simp [shf]
    simp only [hs0, zero_smul, add_zero]
    rw [zS, zV, zW, zG]
    have hf : (fun y => G (0, y))
        = fun y => (Complex.I * g) • (Matrix.of (covDF g A ρ σ ds y) : Mat N) :=
      funext zG
    have hd : Differentiable ℝ (covDF g A ρ σ ds) :=
      (MassGap.CompositesBuild.contDiff_covDF hA g ρ σ ds).differentiable (by simp)
    rw [hf, fderiv_cof (hd z)]
    simp only [covDF, ← Matrix.of_add_of, ← Matrix.smul_of, of_mcomm, smul_add, smul_sub,
      smul_mul_assoc, mul_smul_comm, smul_smul, neg_smul, mul_neg, smul_neg]
    abel

/-- **Every letter**: the continuum letter `phiD` (hence `latD` on the classical configuration, via
`latD_classCfg`) is `a^{|ds|+2} • G`, `G(0, z) = i g D_{ds} F_{ρσ}(z)`.

DERIVED: `2` the dimension of `F`. -/
theorem ord_covDF {A : GPot N} (hA : ContDiff ℝ ∞ A) (g : ℝ) (ρ σ : Fin 4) :
    ∀ ds : List (Fin 4), OrdA (ds.length + 2) (phiD g A ρ σ ds)
      (fun z => (Complex.I * g) • Matrix.of (covDF g A ρ σ ds z))
  | [] => ord_base hA g ρ σ
  | μ :: ds => by
    have := ord_step hA g ρ σ μ ds _ (ord_covDF hA g ρ σ ds)
    rwa [show ds.length + 2 + 1 = (μ :: ds).length + 2 by simp] at this

/-- **A word**: `latW = a^{∑ dim} • Q(a)`, `Q` continuous, `Q(0) = (i g)^{|W|} ∏ D⋯DF`.

DERIVED: `0` the origin. -/
theorem word_ord {A : GPot N} (hA : ContDiff ℝ ∞ A) (g : ℝ) :
    ∀ W : Word, ∃ Q : ℝ → Mat N, Continuous Q ∧
      (∀ a (U : Cfg N), IsClassCfg a g A U → latW U W = a ^ (W.map letDim).sum • Q a) ∧
      Q 0 = (Complex.I * g) ^ W.length •
        (W.map fun l => (Matrix.of (covDF g A l.2.1 l.2.2 l.1 0) : Mat N)).prod
  | [] => ⟨fun _ => 1, continuous_const, fun a U _ => by simp [latW], by simp⟩
  | l :: W => by
    obtain ⟨Q, hQ, eQ, zQ⟩ := word_ord hA g W
    obtain ⟨G, hG, eG, zG⟩ := ord_covDF hA g l.2.1 l.2.2 l.1
    refine ⟨fun a => G (a, 0) * Q a, (hG.continuous.comp
      (continuous_id.prodMk continuous_const)).mul hQ, fun a U hU => ?_, ?_⟩
    · have hW := eQ a U hU
      simp only [latW, List.map_cons, List.prod_cons, List.sum_cons] at hW ⊢
      rw [hW, latD_classCfg hU, site_zero, eG]
      simp only [letDim, smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add]
      rw [Nat.add_comm (List.map letDim W).sum]
    · simp only [List.map_cons, List.prod_cons, List.length_cons]
      rw [zG, zQ, smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ']

theorem negI_mul_pow (g : ℝ) (n : ℕ) :
    (-Complex.I) ^ n * (Complex.I * g) ^ n = ((g ^ n : ℝ) : ℂ) := by
  rw [← mul_pow]
  have h : -Complex.I * (Complex.I * g) = g := by
    have := Complex.I_mul_I
    linear_combination (-(g : ℂ)) * this
  rw [h, Complex.ofReal_pow]

/-- **A factor**. DERIVED: no numeral. -/
theorem fac_ord {A : GPot N} (hA : ContDiff ℝ ∞ A) (g : ℝ) (p : Word × Bool) :
    ∃ q : ℝ → ℝ, Continuous q ∧
      (∀ a (U : Cfg N), IsClassCfg a g A U → facV U p = a ^ (p.1.map letDim).sum * q a) ∧
      q 0 = g ^ p.1.length *
        (if p.2 then (wordTr g A p.1).re else (wordTr g A p.1).im) := by
  obtain ⟨Q, hQ, eQ, zQ⟩ := word_ord hA g p.1
  have htr : Continuous fun a => (-Complex.I) ^ p.1.length * Matrix.trace (Q a) :=
    continuous_const.mul
      (((Matrix.traceLinearMap (Fin N) ℝ ℂ).continuous_of_finiteDimensional).comp hQ)
  have hz : (-Complex.I) ^ p.1.length * Matrix.trace (Q 0)
      = ((g ^ p.1.length : ℝ) : ℂ) * wordTr g A p.1 := by
    rw [zQ, Matrix.trace_smul, smul_eq_mul, ← mul_assoc, negI_mul_pow, wordTr]
  have hfa : ∀ a (U : Cfg N), IsClassCfg a g A U →
      (-Complex.I) ^ p.1.length * Matrix.trace (latW U p.1)
        = ((a ^ (p.1.map letDim).sum : ℝ) : ℂ) * ((-Complex.I) ^ p.1.length * Matrix.trace (Q a)) := by
    intro a U hU
    rw [eQ a U hU, Matrix.trace_smul, Complex.real_smul]
    ring
  cases hb : p.2
  · refine ⟨fun a => ((-Complex.I) ^ p.1.length * Matrix.trace (Q a)).im,
      Complex.continuous_im.comp htr, fun a U hU => ?_, ?_⟩
    · simp only [facV, hb, Bool.false_eq_true, if_false]
      rw [hfa a U hU, Complex.im_ofReal_mul]
    · simp only [hz, Complex.im_ofReal_mul, Bool.false_eq_true, if_false]
  · refine ⟨fun a => ((-Complex.I) ^ p.1.length * Matrix.trace (Q a)).re,
      Complex.continuous_re.comp htr, fun a U hU => ?_, ?_⟩
    · simp only [facV, hb, if_true]
      rw [hfa a U hU, Complex.re_ofReal_mul]
    · simp only [hz, Complex.re_ofReal_mul, if_true]

/-- **A monomial**. DERIVED: no numeral. -/
theorem mono_ord {A : GPot N} (hA : ContDiff ℝ ∞ A) (g : ℝ) :
    ∀ m : CMono, ∃ q : ℝ → ℝ, Continuous q ∧
      (∀ a (U : Cfg N), IsClassCfg a g A U → monoV m U = a ^ cdim m * q a) ∧
      q 0 = g ^ cnF m * cval g A m
  | [] => ⟨fun _ => 1, continuous_const, fun a U _ => by simp [monoV, cdim],
      by simp [cnF, cval]⟩
  | p :: m => by
    obtain ⟨q, hq, eq, zq⟩ := mono_ord hA g m
    obtain ⟨f, hf, ef, zf⟩ := fac_ord hA g p
    refine ⟨fun a => f a * q a, hf.mul hq, fun a U hU => ?_, ?_⟩
    · have hc : cdim (p :: m) = (p.1.map letDim).sum + cdim m := rfl
      rw [monoV_cons, ef a U hU, eq a U hU, hc, pow_add]
      ring
    · have hn : cnF (p :: m) = p.1.length + cnF m := rfl
      have hv : cval g A (p :: m)
          = (if p.2 then (wordTr g A p.1).re else (wordTr g A p.1).im) * cval g A m := rfl
      show f 0 * q 0 = _
      rw [zf, zq, hn, hv, pow_add]
      ring

end Analysis

/-! ## 4. The classical leading terms -/

/-- **Classical leading term of the bare monomial field** for every `m ∈ Ix0`: `m ≠ []` with
every word non-empty. DERIVED: no numeral. -/
theorem classicalLead_bareF (m : CMono) (hm : m ≠ []) (hw : ∀ p ∈ m, p.1 ≠ []) :
    ClassicalLead (N := N) (bareF m).1 (cdim m) (fun A g => g ^ cnF m * cval g A m) := by
  intro A hAdm g U hU
  have hA : ContDiff ℝ ∞ A := contDiff_infty.2 hAdm.1
  obtain ⟨q, hq, eq, zq⟩ := mono_ord hA g m
  beta_reduce
  rw [← zq]
  have hlim : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (q 0)) :=
    hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha' : (0 : ℝ) < a := ha
  rw [bareF_apply, bareF_apply, monoV_one hm hw, eq a (U a) (hU a ha'), sub_zero,
    mul_div_cancel_left₀ _ (pow_ne_zero _ ha'.ne')]

/-- **`TiedB` for the bare monomial fields.** DERIVED: no numeral. -/
theorem tiedB_bareF :
    MassGap.CompositesBuild.TiedB (N := N) (fun i => bareF i.1) :=
  fun i => classicalLead_bareF i.1 i.2.1 i.2.2

/-- **The `tr F F` discretisation**: `bareF (emono β) = −Re tr(latD β₀β₁ · latD β₂β₃)` has classical
leading term `g² Re tr F_{β₀β₁}F_{β₂β₃}` at dimension `4`.

DERIVED: `4` the dimension; `2` the power of `g`. -/
theorem classicalLead_ffT (β : Idx4) :
    ClassicalLead (N := N) (bareF (MassGap.CompositesBuild.emono β)).1 4
      (fun A g => g ^ 2 * ffT g A β) := by
  intro A hA g U hU
  have h := classicalLead_bareF (N := N) (MassGap.CompositesBuild.emono β)
    (by simp [MassGap.CompositesBuild.emono]) (by simp [MassGap.CompositesBuild.emono]) A hA g U hU
  have hd : cdim (MassGap.CompositesBuild.emono β) = 4 := by
    simp [cdim, MassGap.CompositesBuild.emono, letDim]
  have hP : g ^ cnF (MassGap.CompositesBuild.emono β) * cval g A (MassGap.CompositesBuild.emono β)
      = g ^ 2 * ffT g A β := by
    simp [cnF, cval, MassGap.CompositesBuild.emono, wordTr, ffT]
  beta_reduce at h ⊢
  rw [hd, hP] at h
  exact h

/-- **`ClassicalLead` is closed under finite real combinations.** DERIVED: no numeral. -/
theorem classicalLead_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (L : ι → Cfg N → ℝ)
    (P : ι → GPot N → ℝ → ℝ) (d : ℕ) (h : ∀ i ∈ s, ClassicalLead (L i) d (P i)) :
    ClassicalLead (fun U => ∑ i ∈ s, c i * L i U) d (fun A g => ∑ i ∈ s, c i * P i A g) := by
  intro A hA g U hU
  have : (fun a => ((∑ i ∈ s, c i * L i (U a)) - ∑ i ∈ s, c i * L i (fun _ => 1)) / a ^ d)
      = fun a => ∑ i ∈ s, c i * ((L i (U a) - L i (fun _ => 1)) / a ^ d) := by
    funext a
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  beta_reduce
  rw [this]
  exact tendsto_finset_sum s fun i hi => (h i hi A hA g U hU).const_mul (c i)

/-- **The `tr F F` mixing**: basis `bareF (emono β)`, mixing matrices `M k`. Its trace channel
`∑ −Re tr((U_{μν} − 1)²)` is not a multiple of `sym (plaqField q0)`, so it does not serve as the
shared mixing of `ScalarTie`; `ffMixS` adds that field to the basis.

DERIVED: no numeral. -/
def ffMix (M : ℕ → Idx4 → Idx4 → ℝ) : RenormMix N where
  B := Idx4
  op := fun β => bareF (MassGap.CompositesBuild.emono β)
  M := M

/-- The identity matrix on `Idx4`. DERIVED: `1`, `0` the entries. -/
def idM : Idx4 → Idx4 → ℝ := fun β b => if β = b then 1 else 0

/-- **The third clause of `ChannelTie`** for `ffMix` at `Mb = 1`.

DERIVED: `4` the dimension; `2` the power of `g`. -/
theorem ffMix_lead (M : ℕ → Idx4 → Idx4 → ℝ) (β : Idx4) :
    ClassicalLead (fun U => ∑ b, idM β b * ((ffMix (N := N) M).op b).1 U) 4
      (fun A g => g ^ 2 * ffT g A β) := by
  have h : (fun U => ∑ b, idM β b * ((ffMix (N := N) M).op b).1 U)
      = (bareF (N := N) (MassGap.CompositesBuild.emono β)).1 := by
    funext U
    simp [idM, ffMix]
  rw [h]
  exact classicalLead_ffT β

/-- **A whole `ChannelTie` for `ffMix`** at every hypercubic-equivariant `Z`: the mixing
`M k α b = ∑_β Z k α β 1_{β b}`. This is `ChannelTie` in isolation; `ffMix` is not a mixing for
which `ScalarTie` holds. DERIVED: no numeral. -/
theorem channelTie_ffMixZ (Z : ℕ → Idx4 → Idx4 → ℝ)
    (hZ : ∀ k (A : Matrix (Fin 4) (Fin 4) ℝ), IsHyp A → ∀ c,
      zAct (Z k) (rotC A c) = rotC A (zAct (Z k) c)) :
    ChannelTie (ffMix (N := N) (fun k α b => ∑ β, Z k α β * idM β b)) idM Z :=
  ⟨fun _ _ _ => rfl, hZ, fun β => ffMix_lead _ β⟩

/-- **A whole `ChannelTie` for `ffMix`** at a scalar renormalisation `Z k = z k • 1`: the mixing
`M k α b = z k · 1_{α b}`. This is `ChannelTie` in isolation. DERIVED: no numeral. -/
theorem channelTie_ffMix (z : ℕ → ℝ) :
    ChannelTie (ffMix (N := N) (fun k α b => z k * idM α b)) idM (fun k α b => z k * idM α b) := by
  refine ⟨fun k α b => ?_, fun k R _ c => ?_, fun β => ffMix_lead _ β⟩
  · show z k * idM α b = ∑ β, z k * idM α β * idM β b
    simp [idM]
  · have hz : ∀ c' : Idx4 → ℝ, zAct (fun α b => z k * idM α b) c' = fun β => z k * c' β := by
      intro c'
      funext β
      simp [zAct, idM, mul_ite, Finset.sum_ite_eq']
      ring
    rw [hz, hz]
    funext β
    simp only [rotC, Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => by ring

/-- **The `tr F F` mixing with the observer's field in the basis**: basis `Idx4 ⊕ Unit`, the
fields `bareF (emono β)` and `sym (plaqField q0)`. DERIVED: `0` the plaquette `q0`. -/
def ffMixS (M : ℕ → Idx4 → Idx4 ⊕ Unit → ℝ) : RenormMix N where
  B := Idx4 ⊕ Unit
  op := Sum.elim (fun β => bareF (MassGap.CompositesBuild.emono β))
    (fun _ => MassGap.ObserverSymField.sym
      (MassGap.ObserverEnergyMoments.plaqField MassGap.ObserverEnergyMoments.q0))
  M := M

/-- The bare coefficients on `Idx4 ⊕ Unit`: the identity on the tensor fields, `0` on the
observer's field. DERIVED: `0` the coefficient. -/
def idMS : Idx4 → Idx4 ⊕ Unit → ℝ := fun β => Sum.elim (idM β) (fun _ => 0)

/-- **The third clause of `ChannelTie`** for `ffMixS` at `Mb = idMS`.

DERIVED: `4` the dimension; `2` the power of `g`. -/
theorem ffMixS_lead (M : ℕ → Idx4 → Idx4 ⊕ Unit → ℝ) (β : Idx4) :
    ClassicalLead (fun U => ∑ b, idMS β b * ((ffMixS (N := N) M).op b).1 U) 4
      (fun A g => g ^ 2 * ffT g A β) := by
  have h : (fun U => ∑ b, idMS β b * ((ffMixS (N := N) M).op b).1 U)
      = (bareF (N := N) (MassGap.CompositesBuild.emono β)).1 := by
    funext U
    simp [idMS, idM, ffMixS, Fintype.sum_sum_type]
  rw [h]
  exact classicalLead_ffT β

/-- **A whole `ChannelTie` for `ffMixS`** at every hypercubic-equivariant `Z`: the mixing
`M k α b = ∑_β Z k α β idMS β b`. `ScalarTie` is not proved here. DERIVED: no numeral. -/
theorem channelTie_ffMixS (Z : ℕ → Idx4 → Idx4 → ℝ)
    (hZ : ∀ k (A : Matrix (Fin 4) (Fin 4) ℝ), IsHyp A → ∀ c,
      zAct (Z k) (rotC A c) = rotC A (zAct (Z k) c)) :
    ChannelTie (ffMixS (N := N) (fun k α b => ∑ β, Z k α β * idMS β b)) idMS Z :=
  ⟨fun _ _ _ => rfl, hZ, fun β => ffMixS_lead _ β⟩

#print axioms hadamard
#print axioms ord_covDF
#print axioms classicalLead_bareF
#print axioms tiedB_bareF
#print axioms classicalLead_ffT
#print axioms classicalLead_sum
#print axioms ffMix_lead
#print axioms channelTie_ffMix
#print axioms channelTie_ffMixZ
#print axioms ffMixS_lead
#print axioms channelTie_ffMixS

end MassGap.ClassicalLimit
