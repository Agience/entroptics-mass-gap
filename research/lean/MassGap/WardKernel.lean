import Mathlib
import MassGap.ObsLead

/-!
# MassGap.WardKernel — what `hK` and `hNG` read at the data `rhoD f z`, and how the stress insertion in `hWard` splits

`ObsLead.clayStatementAt_SU_obs` takes `hK : TwoPointKernel (rhoD (fT N) z) G`,
`hAF : AFCoefficient N G` and `hWard : WardT (rhoD (fT N) z)`. This module computes which basis
fields of `rhoD f z` the trace and the stress tensor read, at every step `k`.

## The trace

`mixC_trC_rhoD`: the trace `trC` has coefficient `(N/16) z_sc k` on the observer's field
`obs = sym (plaqField q0)` and `0` on every channel field. Hence (`latT_trace_rhoD_obsConn`) at every step

  `latT (rhoD f z) k ((trC, uᵢ)ᵢ) = ((N/16) z_sc k)ⁿ · latSk k ((obs − ν_k(obs), uᵢ)ᵢ)`,

and `contTr (rhoD f z) u` is the `ultra`-limit of the right side (`contTr_rhoD`). So:

* `twoPointKernel_rhoD_iff`: `TwoPointKernel (rhoD f z) G` is the statement that the connected
  two-point function of `obs` in the Wilson states `stateK k`, times `((N/16) z_sc k)²`, has
  `ultra`-limit `∫∫ f(x) g(y) G(|x − y|)` on separated continuous test functions;
* `twoPointKernel_rhoD_congr`, `nonGaussianT_rhoD_congr`: `TwoPointKernel` and `NonGaussianT` at
  `rhoD f z` depend on `z` only through `z_sc` and not at all on the tensor fields `f`.

None of these involve the flow `W`.

## The stress tensor

`stressC κ μ ν = stressC 0 μ ν + (κ/4) δ_{μν} trC` (`stressC_split`), and the reading `latT` is
linear in the coefficient tensor of one insertion (`latT_cons_add_smul`), so
`latT_stress_split`: the insertion of `Θ_{μν}` is the insertion of the traceless `stressC 0 μ ν`
plus `(κ/4) δ_{μν}` times the insertion of the trace. At `rhoD f z`:

* `mixC_stressC_none`: `Θ_{μν}` has coefficient `(κ/4) δ_{μν} (N/16) z_sc k` on `obs`;
* `mixC_stressC_some`: on the channel field `opT f c γ` it has coefficient
  `π(ric(Rl e_γ))_{μν} · z_ri k` for `c = ri` and `0` for the scalar, pseudoscalar and Weyl channels;
* so `stressC 0 μ ν` reads only the traceless-Ricci channel, with factor `z_ri k`
  (`mixC_stress0_none`, and `mixC_stressC_some` at `κ = 0`).

The contraction lemmas behind these: `ricC μ ν ⬝ y = ric y μ ν` (`ricC_dot`), `ric (Rl x)` is
symmetric (`ric_Rl_symm`), `ric ∘ P c` vanishes for `c = ps, we` and is `π ∘ ric ∘ Rl` for `c = ri`
(`ricC_dot_P_ps`, `ricC_dot_P_we`, `ricC_dot_P_ri`), `⟨t, t⟩ = 24`, `⟨trC, t⟩ = 12`.

## The capstone with the kernel on the observer's field

`clayStatementAt_SU_obsKernel` is `ObsLead.clayStatementAt_SU_obs` with `hK` replaced by its
equivalent `twoPointKernel_rhoD_iff` form, a statement on `obs` and `z_sc` only.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `16 = 8 · 2` as in `ClayData.coefC_mD`; `24 = 2 · 3 · 4` the norm of `t`
(`ric t = 3 δ`, `tr δ = 4`); `12 = 24/2`; `4` the dimension in `(κ − 1)/4` and `κ/4`; `2` the number
of trace insertions in a two-point function; `0`, `1` the coefficient values and the unit tensor
entries.
-/

noncomputable section

namespace MassGap.WardKernel

open MassGap MassGap.ClayStatement MassGap.ClayData MassGap.ClayWiring MassGap.InfiniteLattice
  MassGap.ContinuumField MassGap.ContinuumSchwinger Filter
open scoped Topology Matrix

variable {N : ℕ}

/-! ## 1. The trace reads only the observer's field -/

section Trace

/-- The connected observer's field `obs − ν_k(obs)` with a test function.

DERIVED: no numeral. -/
def obsConn (hN : N ≠ 0) (k : ℕ) (u : TestFn) : SField N :=
  ((ClayData.obs N).sub (stateK hN k (ClayData.obs N).1), u)

/-- The basis field `none` of `rhoD f z`, connected, is `obsConn`. DERIVED: no numeral. -/
theorem locField_none (hN : N ≠ 0) (ft : Idx4 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ)
    (k : ℕ) (u : TestFn) : locField hN (rhoD ft z) k (none : BD) u = obsConn hN k u := rfl

/-- DERIVED: no numeral. -/
theorem mixC_rhoD (ft : Idx4 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ) (k : ℕ)
    (c : Idx4 → ℝ) (b : BD) : mixC (rhoD ft z) k c b = coefC (mD N) c b * ZD z k (opD ft b) :=
  mixC_mixOfZ (opD ft) (mD N) (ZD z) k c b

/-- **The trace coefficients of `rhoD f z` at step `k`**: `(N/16) z_sc k` on `obs`, `0` on every
channel field.

DERIVED: `16` as in `ClayData.coefC_mD`; `0` the other coefficients. -/
theorem mixC_trC_rhoD (hN : N ≠ 0) (ft : Idx4 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ)
    (k : ℕ) (b : BD) :
    mixC (rhoD ft z) k trC b = if b = none then (N : ℝ) / 16 * z .sc k else 0 := by
  rw [mixC_rhoD, coefC_mD N hN b]
  cases b with
  | none => rw [if_pos rfl, if_pos rfl, opD_none, ZD_obs]
  | some p => rw [if_neg (Option.some_ne_none p), if_neg (Option.some_ne_none p), zero_mul]

/-- **The lattice reading of `n` trace insertions** is `((N/16) z_sc k)ⁿ` times the lattice
`n`-point function of the connected observer's field.

DERIVED: `16` as in `mixC_trC_rhoD`. -/
theorem latT_trace_rhoD_obsConn (hN : N ≠ 0) (ft : Idx4 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ)
    (k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → TestFn) :
    latT hN (rhoD ft z) k (fun i => (trC, u i))
      = ((N : ℝ) / 16 * z .sc k) ^ Fintype.card ι * latSk hN k (fun i => obsConn hN k (u i)) := by
  show ∑ b : ι → BD, (∏ i, mixC (rhoD ft z) k trC (b i))
      * latSk hN k (fun i => locField hN (rhoD ft z) k (b i) (u i)) = _
  rw [Finset.sum_eq_single (fun _ => (none : BD))]
  · have h1 : ∀ i : ι, mixC (rhoD ft z) k trC ((fun _ => (none : BD)) i)
        = (N : ℝ) / 16 * z .sc k := fun i => by
      rw [mixC_trC_rhoD hN, if_pos rfl]
    rw [Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_const, Finset.card_univ]
    rfl
  · intro b _ hb
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ none := by
      by_contra h
      exact hb (funext fun j => not_not.1 fun hj => h ⟨j, hj⟩)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [mixC_trC_rhoD hN, if_neg hi]), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The trace's Schwinger function at `rhoD f z`** is the `ultra`-limit of `((N/16) z_sc k)ⁿ`
times the lattice `n`-point function of the connected observer's field.

DERIVED: `16` as in `mixC_trC_rhoD`. -/
theorem contTr_rhoD (hN : N ≠ 0) (ft : Idx4 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ)
    {n : ℕ} (u : Fin n → TestFn) :
    contTr hN (rhoD ft z) u = limUnder (ultra : Filter ℕ)
      (fun k => ((N : ℝ) / 16 * z .sc k) ^ n * latSk hN k (fun i => obsConn hN k (u i))) := by
  show limUnder (ultra : Filter ℕ) (fun k => latT hN (rhoD ft z) k (fun i => (trC, u i))) = _
  congr 1
  funext k
  rw [latT_trace_rhoD_obsConn hN, Fintype.card_fin]

/-- The trace's Schwinger functions depend on `z` only through `z_sc`, and not on `f`.

DERIVED: no numeral. -/
theorem contTr_rhoD_congr (hN : N ≠ 0) (ft ft' : Idx4 → LField (MassGap.SUN.SU N))
    (z z' : Chan → ℕ → ℝ) (h : z .sc = z' .sc) {n : ℕ} (u : Fin n → TestFn) :
    contTr hN (rhoD ft z) u = contTr hN (rhoD ft' z') u := by
  rw [contTr_rhoD, contTr_rhoD, h]

/-- **`TwoPointKernel` at `rhoD f z` is a statement on the observer's field**: `G` continuous on
`(0, ∞)` and, on separated continuous test functions, the `ultra`-limit of
`((N/16) z_sc k)² ⟨(obs − ν_k obs)(f) (obs − ν_k obs)(g)⟩_k` is `∫∫ f(x) g(y) G(|x − y|)`.

DERIVED: `2` the order; `16` as in `mixC_trC_rhoD`; `0` the sign of the separation. -/
theorem twoPointKernel_rhoD_iff (hN : N ≠ 0) (ft : Idx4 → LField (MassGap.SUN.SU N))
    (z : Chan → ℕ → ℝ) (G : ℝ → ℝ) :
    TwoPointKernel hN (rhoD ft z) G ↔ ContinuousOn G (Set.Ioi 0)
      ∧ ∀ f g : TestFn, Continuous f.1 → Continuous g.1 →
        (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f g) →
        limUnder (ultra : Filter ℕ) (fun k => ((N : ℝ) / 16 * z .sc k) ^ 2
            * latSk hN k (fun i => obsConn hN k (![f, g] i)))
          = ∫ x, ∫ y, f.1 x * g.1 y * G (ContinuumNontrivial.eDist x y) := by
  unfold TwoPointKernel
  simp only [contTr_rhoD hN ft z]

/-- **`TwoPointKernel` at `rhoD f z` does not see `f` or the factors other than `z_sc`.**

DERIVED: no numeral. -/
theorem twoPointKernel_rhoD_congr (hN : N ≠ 0) (ft ft' : Idx4 → LField (MassGap.SUN.SU N))
    (z z' : Chan → ℕ → ℝ) (h : z .sc = z' .sc) (G : ℝ → ℝ) :
    TwoPointKernel hN (rhoD ft z) G ↔ TwoPointKernel hN (rhoD ft' z') G := by
  unfold TwoPointKernel
  simp only [contTr_rhoD_congr hN ft ft' z z' h]

/-- **`NonGaussianT` at `rhoD f z` does not see `f` or the factors other than `z_sc`.**

DERIVED: no numeral. -/
theorem nonGaussianT_rhoD_congr (hN : N ≠ 0) (ft ft' : Idx4 → LField (MassGap.SUN.SU N))
    (z z' : Chan → ℕ → ℝ) (h : z .sc = z' .sc) :
    NonGaussianT hN (rhoD ft z) ↔ NonGaussianT hN (rhoD ft' z') := by
  unfold NonGaussianT cum3T
  simp only [contTr_rhoD_congr hN ft ft' z z' h]

end Trace

/-! ## 2. Contractions -/

section Contract

/-- The two-index tensor with the single unit entry `(μ, ν)`. DERIVED: `1`, `0` the entries. -/
def eS (μ ν : Fin 4) : S2 := fun a b => if a = μ ∧ b = ν then 1 else 0

/-- `ricC μ ν = kt (eS μ ν)`. DERIVED: no numeral. -/
theorem ricC_eq_kt (μ ν : Fin 4) : ricC μ ν = kt (eS μ ν) := by
  funext α
  simp only [ricC, kt, eS]
  by_cases h3 : α 3 = α 1
  · rw [h3, dl_self, mul_one]
    by_cases h0 : α 0 = μ <;> by_cases h2 : α 2 = ν <;> simp [h0, h2]
  · rw [dl_ne (fun h => h3 h.symm), mul_zero]
    simp [h3]

/-- **`⟨ricC μ ν, y⟩ = ric y μ ν`.** DERIVED: no numeral. -/
theorem ricC_dot (μ ν : Fin 4) (y : V4) : ricC μ ν ⬝ᵥ y = ric y μ ν := by
  rw [ricC_eq_kt, kt_dot]
  simp only [dotS, eS]
  rw [Finset.sum_eq_single μ, Finset.sum_eq_single ν]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro a _ ha
    exact Finset.sum_eq_zero fun b _ => by simp [ha]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ric_smul (c : ℝ) (x : V4) : ric (c • x) = c • ric x := ricL.map_smul c x

theorem ric_sub (x y : V4) : ric (x - y) = ric x - ric y := ricL.map_sub x y

/-- **The Ricci contraction of a tensor with the Riemann symmetries is symmetric.**

DERIVED: no numeral. -/
theorem ric_Rl_symm (x : V4) (a b : Fin 4) : ric (Rl x) a b = ric (Rl x) b a := by
  show ∑ l, rsym x ![a, l, b, l] = ∑ l, rsym x ![b, l, a, l]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← rsym_pairEx x ![b, l, a, l]]
  rfl

/-- `⟨t, t⟩ = 24`. DERIVED: `24 = 2 · 3 · 4`. -/
theorem tv_dot_tv : tv ⬝ᵥ tv = 24 := by
  rw [tv_dot, Rl_tv, ric_tv, trS_smul, trS_dS]
  norm_num

/-- `⟨trC, t⟩ = 12`. DERIVED: `12 = 24/2`. -/
theorem trC_dot_tv : trC ⬝ᵥ tv = 12 := by
  rw [trC_dot_Rl tv Rl_tv, tv_dot_tv]
  norm_num

/-- DERIVED: `4` the dimension. -/
theorem ric_PSl (x : V4) : ric (PSl x) = (trS (ric (Rl x)) / 4) • dS := by
  rw [PSl_apply, ric_smul, ric_tv, smul_smul, tv_dot, tv_dot_tv]
  congr 1
  ring

theorem ric_PEl (x : V4) : ric (PEl x) = 0 := by
  rw [PEl_apply, ric_smul, ric_eps, smul_zero]

theorem ric_Ql (x : V4) : ric (Ql x) = piS (ric (Rl x)) := by
  rw [Ql_apply, ric_smul, ric_Rl_kt_piS, smul_smul]
  norm_num

/-- **The Weyl channel has no Ricci contraction.** DERIVED: no numeral. -/
theorem ric_P_we (x : V4) : ric (P .we x) = 0 := by
  have e : P .we x = Rl x - PSl x - PEl x - Ql x := rfl
  rw [e, ric_sub, ric_sub, ric_sub, ric_PSl, ric_PEl, ric_Ql]
  funext a b
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, piS, dS,
    ric_Rl_symm x b a]
  ring

theorem ricC_dot_P_ps (μ ν : Fin 4) (x : V4) : ricC μ ν ⬝ᵥ P .ps x = 0 := by
  rw [ricC_dot]
  show ric (PEl x) μ ν = 0
  rw [ric_PEl]
  rfl

theorem ricC_dot_P_we (μ ν : Fin 4) (x : V4) : ricC μ ν ⬝ᵥ P .we x = 0 := by
  rw [ricC_dot, ric_P_we]
  rfl

theorem ricC_dot_P_ri (μ ν : Fin 4) (x : V4) :
    ricC μ ν ⬝ᵥ P .ri x = piS (ric (Rl x)) μ ν := by
  rw [ricC_dot]
  show ric (Ql x) μ ν = _
  rw [ric_Ql]

end Contract

/-! ## 3. The stress tensor at `rhoD f z` -/

section Stress

/-- DERIVED: `4` the dimension. -/
theorem stressC_eq (κ : ℝ) (μ ν : Fin 4) :
    stressC κ μ ν = ricC μ ν + (if μ = ν then (κ - 1) / 4 else 0) • trC := by
  funext α
  simp only [stressC, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- **`Θ_{μν} = Θ⁰_{μν} + (κ/4) δ_{μν} tr`**, `Θ⁰ = stressC 0` traceless.

DERIVED: `4` the dimension; `1`, `0` the Kronecker values. -/
theorem stressC_split (κ : ℝ) (μ ν : Fin 4) :
    stressC κ μ ν = stressC 0 μ ν + (κ / 4 * (if μ = ν then 1 else 0)) • trC := by
  funext α
  simp only [stressC, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem coefC_none (x : V4) : coefC (mD N) x none = wD N * (x ⬝ᵥ tv) := by
  simp only [coefC, mD_none, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem coefC_some (x : V4) (c : Chan) (γ : Idx4) :
    coefC (mD N) x (some (c, γ)) = if c = .sc then 0 else x ⬝ᵥ P c (Pi.single γ 1) := by
  by_cases hc : c = .sc
  · simp [coefC, mD_some, hc]
  · simp only [coefC, mD_some, hc, if_false]
    rw [vec_Pm]

/-- **The coefficient of `Θ_{μν}` on the observer's field**: `(κ/4) δ_{μν} (N/16) z_sc k`.

DERIVED: `4` the dimension; `16` as in `mixC_trC_rhoD`; `24`, `12` as in `tv_dot_tv`,
`trC_dot_tv`. -/
theorem mixC_stressC_none (ft : Idx4 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ) (k : ℕ)
    (κ : ℝ) (μ ν : Fin 4) :
    mixC (rhoD ft z) k (stressC κ μ ν) none
      = κ / 4 * (if μ = ν then 1 else 0) * ((N : ℝ) / 16 * z .sc k) := by
  rw [mixC_rhoD, opD_none, ZD_obs, coefC_none, stressC_eq, add_dotProduct, smul_dotProduct,
    ricC_dot, ric_tv, trC_dot_tv, wD_def, tv_dot_tv]
  by_cases h : μ = ν
  · rw [if_pos h, if_pos h]
    subst h
    simp only [Pi.smul_apply, smul_eq_mul, dS, dl_self]
    ring
  · rw [if_neg h, if_neg h]
    simp only [Pi.smul_apply, smul_eq_mul, dS, dl_ne h]
    ring

/-- **The traceless part `Θ⁰` has no coefficient on the observer's field.**

DERIVED: `0` the value. -/
theorem mixC_stress0_none (ft : Idx4 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ) (k : ℕ)
    (μ ν : Fin 4) : mixC (rhoD ft z) k (stressC 0 μ ν) none = 0 := by
  rw [mixC_stressC_none]
  ring

/-- **The coefficient of `Θ_{μν}` on the channel field `opT f c γ`**: `π(ric(Rl e_γ))_{μν} z_ri k`
on the traceless-Ricci channel and `0` on the others.

DERIVED: `0` the other coefficients. -/
theorem mixC_stressC_some (ft : Idx4 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ) (k : ℕ)
    (κ : ℝ) (μ ν : Fin 4) (c : Chan) (γ : Idx4) :
    mixC (rhoD ft z) k (stressC κ μ ν) (some (c, γ))
      = if c = .ri then piS (ric (Rl (Pi.single γ 1))) μ ν * z .ri k else 0 := by
  rw [mixC_rhoD, opD_some, ZD_opT, coefC_some]
  cases c with
  | sc => simp
  | ps =>
    rw [if_neg (by decide : Chan.ps ≠ Chan.sc), if_neg (by decide : Chan.ps ≠ Chan.ri), stressC_eq,
      add_dotProduct, smul_dotProduct, trC_dot_P Chan.ps (by decide), smul_zero, add_zero,
      ricC_dot_P_ps, zero_mul]
  | ri =>
    rw [if_neg (by decide : Chan.ri ≠ Chan.sc), if_pos rfl, stressC_eq, add_dotProduct,
      smul_dotProduct, trC_dot_P Chan.ri (by decide), smul_zero, add_zero, ricC_dot_P_ri]
  | we =>
    rw [if_neg (by decide : Chan.we ≠ Chan.sc), if_neg (by decide : Chan.we ≠ Chan.ri), stressC_eq,
      add_dotProduct, smul_dotProduct, trC_dot_P Chan.we (by decide), smul_zero, add_zero,
      ricC_dot_P_we, zero_mul]

/-- `mixC` is linear in the coefficient tensor. DERIVED: no numeral. -/
theorem mixC_add_smul (ρ : RenormMix N) (k : ℕ) (c₁ c₂ : Idx4 → ℝ) (s : ℝ) (b : ρ.B) :
    mixC ρ k (c₁ + s • c₂) b = mixC ρ k c₁ b + s * mixC ρ k c₂ b := by
  simp only [mixC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

/-- **The lattice reading is linear in the coefficient tensor of the first insertion.**

DERIVED: `1` the first insertion. -/
theorem latT_cons_add_smul (hN : N ≠ 0) (ρ : RenormMix N) (k : ℕ) {n : ℕ} (c₁ c₂ : Idx4 → ℝ)
    (s : ℝ) (u : TestFn) (F : Fin n → TDatum) :
    latT hN ρ k (Fin.cons (α := fun _ => TDatum) (c₁ + s • c₂, u) F)
      = latT hN ρ k (Fin.cons (α := fun _ => TDatum) (c₁, u) F)
        + s * latT hN ρ k (Fin.cons (α := fun _ => TDatum) (c₂, u) F) := by
  unfold latT
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have e : ∀ c : Idx4 → ℝ,
      (fun i => locField hN ρ k (b i) ((Fin.cons (α := fun _ => TDatum) (c, u) F) i).2)
        = fun i => locField hN ρ k (b i) ((Fin.cons (α := fun _ => TDatum) (c₁, u) F) i).2 := by
    intro c
    funext i
    cases i using Fin.cases <;> rfl
  rw [e (c₁ + s • c₂), e c₂]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mixC_add_smul]
  ring

/-- **The insertion of `Θ_{μν}` splits** into the insertion of the traceless `Θ⁰_{μν}` and
`(κ/4) δ_{μν}` times the insertion of the trace, at every step and for every mixing.

DERIVED: `4` the dimension; `1`, `0` the Kronecker values. -/
theorem latT_stress_split (hN : N ≠ 0) (ρ : RenormMix N) (k : ℕ) {n : ℕ} (κ : ℝ) (μ ν : Fin 4)
    (u : TestFn) (F : Fin n → TDatum) :
    latT hN ρ k (Fin.cons (α := fun _ => TDatum) (stressC κ μ ν, u) F)
      = latT hN ρ k (Fin.cons (α := fun _ => TDatum) (stressC 0 μ ν, u) F)
        + κ / 4 * (if μ = ν then 1 else 0)
          * latT hN ρ k (Fin.cons (α := fun _ => TDatum) (trC, u) F) := by
  rw [stressC_split κ μ ν, latT_cons_add_smul]

end Stress

/-! ## 4. The capstone with the kernel on the observer's field -/

section Capstone

open MassGap.ContinuumFlow MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ObserverSymField

/-- **`ObsLead.clayStatementAt_SU_obs` with the kernel input on the observer's field**: `hKc`,
`hKo` are `TwoPointKernel (rhoD (fT N) z) G` in the form `twoPointKernel_rhoD_iff`, on the
connected two-point function of `obs` in the Wilson states and `z_sc` only. The other inputs are
those of `clayStatementAt_SU_obs`.

DERIVED: `2` the least colour count, the limits of the scalar and pseudoscalar factors and the
order of the kernel; `16` as in `mixC_trC_rhoD`; `0` the plane and the sign of the separation;
`4` the dimension. -/
theorem clayStatementAt_SU_obsKernel (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (z : Chan → ℕ → ℝ) (hz : ∀ c k, z c k ≠ 0)
    (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (hzP : Tendsto (fun k => z .ps k * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hKc : ContinuousOn G (Set.Ioi 0))
    (hKo : ∀ f g : TestFn, Continuous f.1 → Continuous g.1 →
      (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f g) →
      limUnder (ultra : Filter ℕ) (fun k => ((N : ℝ) / 16 * z .sc k) ^ 2
          * latSk (ne_zero_of_two_le hN2) k
              (fun i => obsConn (ne_zero_of_two_le hN2) k (![f, g] i)))
        = ∫ x, ∫ y, f.1 x * g.1 y * G (ContinuumNontrivial.eDist x y))
    (hAF : AFCoefficient N G)
    (hNG : NonGaussianT (ne_zero_of_two_le hN2) (rhoD (fT N) z))
    (hWard : WardT (ne_zero_of_two_le hN2) (rhoD (fT N) z))
    (hCO : CompOS (ne_zero_of_two_le hN2) (build (rhoD (fT N) z) (bareD (fT N) (bT N))))
    (wC : TSepG (build (rhoD (fT N) z) (bareD (fT N) (bT N))).Ix 0 →
      preH (ne_zero_of_two_le hN2) W hU hphys)
    (hLC : LinkCPre (ne_zero_of_two_le hN2) 0
      (preVac (ne_zero_of_two_le hN2) W hU hphys)
      (preTime (ne_zero_of_two_le hN2) W hU hphys)
      (build (rhoD (fT N) z) (bareD (fT N) (bT N))) wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) (rhoD (fT N) z)
          (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT (ne_zero_of_two_le hN2) (rhoD (fT N) z)
            (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1 Q.1.1))
        ∧ inner ℂ (LinkReduce.wOfC eI wC P)
            (preCvec (ne_zero_of_two_le hN2) W hU hphys Q)
          = (mixT (ne_zero_of_two_le hN2) (rhoD (fT N) z)
              (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1 Q.1.1 : ℂ)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_SU_obs hN2 W ht hU hphys hfar z hz hzS hzP G
    ((twoPointKernel_rhoD_iff (ne_zero_of_two_le hN2) (fT N) z G).2 ⟨hKc, hKo⟩) hAF hNG hWard
    hCO wC hLC hX

end Capstone

end MassGap.WardKernel

end

#print axioms MassGap.WardKernel.mixC_trC_rhoD
#print axioms MassGap.WardKernel.latT_trace_rhoD_obsConn
#print axioms MassGap.WardKernel.contTr_rhoD
#print axioms MassGap.WardKernel.twoPointKernel_rhoD_iff
#print axioms MassGap.WardKernel.twoPointKernel_rhoD_congr
#print axioms MassGap.WardKernel.nonGaussianT_rhoD_congr
#print axioms MassGap.WardKernel.ricC_dot
#print axioms MassGap.WardKernel.ric_P_we
#print axioms MassGap.WardKernel.mixC_stressC_none
#print axioms MassGap.WardKernel.mixC_stressC_some
#print axioms MassGap.WardKernel.latT_stress_split
#print axioms MassGap.WardKernel.clayStatementAt_SU_obsKernel
