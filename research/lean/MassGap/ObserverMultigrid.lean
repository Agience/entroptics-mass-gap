import Mathlib
import MassGap.ObserverFlowSUN
import MassGap.ScaleSatisfiable

/-!
# MassGap.ObserverMultigrid — the multigrid observer: strided block steps, no held boundary

The observer `ObserverFlowSUN.sunFam hN2 c hc0 hc s₀` computes each output link by `⌊(s₀/a)²⌋` block steps
inside its own box of half-width `⌊s₀/a⌋`, the links outside the box held at their bare values
(`ObserverFlowSUN.obsFlowG`). This module builds an observer of the same physical reach that holds no link
fixed: a composite of global smoothing steps, one group of `m` steps per scale, the stride doubling from
scale to scale. Declarations are in the namespace `MassGap.ObserverMultigrid`.

## 1. The strided step

* `sh ν n x` is the site `x + n ν̂`; `ptr U ν n x` is the parallel transporter along the straight path of
  `n` links from `x` in direction `ν` (`ptr_snoc`, `ptr_gauge`, `ptr_agree`, `continuous_ptr`; under the time
  reflection `ptr_refl_ne` for `ν ≠ τ` and `ptr_refl_eq` for `ν = τ`, where the path is reversed).
* `stapleD U d μ x p` is the stride-`d` staple beside the link `(μ, x)`: transverse direction
  `ν = other μ p.1`, side `p.2`; the path `x → x ± dν̂ → x ± dν̂ + μ̂ → x + μ̂`, its two transverse legs
  stride-`d` transporters of fine links. At `d = 1` it has the value of the plaquette staple
  `ObserverFlowSUN.stapleG` (a remark; no lemma states it).
* `mgStep B d` replaces every link by the block step `B` (`ObserverFlowSUN.BlockStep`, e.g.
  `ObserverFlowSUN.sunBlockStep`) of itself and its six stride-`d` staples. It is applied at every link;
  no link is exempt. Proved: gauge covariance (`mgStep_gauge`), time-reflection covariance (`mgStep_refl`,
  the staple sides swapped by `ReflApe.stapleSwap` as for the plaquette step), continuity
  (`continuous_mgStep`), and at `d ≥ 1` the output at a link reads only links whose base lies within `d`
  of it in every coordinate (`mgStep_reads`).

## 2. The multigrid map and its light cone

`mgMap B m J = (mgStep B 2^{J−1})^[m] ∘ ⋯ ∘ (mgStep B 1)^[m]`: `m` global steps at stride `1`, then `m` at
stride `2`, …, then `m` at stride `2^{J−1}` (`mgMap_succ`, by definition). Each level acts on the output of
the level below it, a configuration on all of `ℤ⁴`; no level reads a bare link other than through that
configuration. `ReadsWithin F R` says the output of `F` at a link is a function of the input on the links
whose base lies within `R` of it; it composes (`ReadsWithin.comp`, ranges add) and iterates
(`ReadsWithin.iterate`). So `mgMap B m J` reads within `mgRange m J = m (2^J − 1)`
(`mgMap_reads`, `mgRange_add`): a geometric sum, dominated by the coarsest stride. Gauge covariance,
reflection covariance and continuity pass to the composite (`mgMap_gauge`, `mgMap_refl`,
`continuous_mgMap`). `mgConfFlow B m J` is the `ContinuumFlow.ConfFlow` with `V k = mgMap B m (J k)` and
range `mgRange m (J k)`.

## 3. The family

The stride-`d` staple is a `d × 1` rectangle: it does not average across a block, and in the `μ`-direction
it stays one lattice step. `sunBlockStep` weights it with the same `c` as a plaquette staple, so at the
coarsest level (`d ≈ s/(2 m a_k)`) one long thin loop carries the full edge weight. Whether the levels give a
smoothing kernel of physical width `s`, rather than a sparse long-range coupling, is not shown.

`mgFam hN c hc0 hc m s = mgConfFlow (sunBlockStep hN c hc0 hc) m (mgLevels N m s)`, with
`J_k = mgLevels N m s k = log₂ ⌊s / (m a_k)⌋`: the coarsest stride `2^{J_k − 1}` is at most
`s / (2 m a_k)`, and the number of levels grows like `log₂ (s/a_k)`. Proved:

* **`spacing_mul_mgRange_le`**: `a_k · mgRange m J_k ≤ s` at every step `k` (`0 ≤ s`).
* **`mgFam_physRange`**: `(CompositeLink.Φ0 (mgFam … m s)).PhysRange r` at every `r ≥ s ≥ 0`; the shape of
  `ObserverFlowSUN.sunFam_physRange`, the hypothesis `s < r` relaxed to `s ≤ r`.
* `mgFam_V_of_lt`, `mgFam_eventually_id`: the identity at a step with `s < 2 m a_k`, and at each fixed step
  as `s → 0⁺` (`m ≥ 1`).
* **Non-degeneracy.** `sunStep_moves_one`: for `c > 0` the `SU(N)` block step with six identity staples
  moves the link `diag(i, −i, 1, …, 1)`. `mgStep_moves`: any block step that moves some link against six
  identity staples moves a configuration at every stride `d ≥ 1` (the configuration equal to `1` except at
  one link, whose stride-`d` staples are all `1`). `mgStep_sun_moves`: `mgStep (sunBlockStep …) d` moves a
  configuration at every `d ≥ 1`, `c > 0`. `mgFam_moves`: at `m = 1` and a step with `J_k = 1`,
  `(mgFam … 1 s).V k` moves a configuration. In particular `¬ ∀ᶠ k, (mgFam … m s).V k = id` (`s > 0`), which
  `ScaleIdentityNoGo.not_substrateCoreAt_of_id` needs excluded for `MW` to be satisfiable, is not proved.

## 4. The scale input at this observer (stated)

`MW W` is the observer's moment condition `(M_W)` of `ScaleSatisfiable`:
`∃ t > 0, ∃ C, ∀ᶠ k, ScaleAt (fun _ => W) t C 0 0 k 1`. `mw_iff` restates
`ScaleSatisfiable.scaleControlAll_one_iff` (a family with `Wf 1 = W` meeting `ScaleControlAll 1` exists iff
`MW W`); `substrateCoreAt_of_MW` gives the substrate core at the constant family from `MW W` and `af`.
`MW (mgFam hN2 c hc0 hc m s₀)` is refuted (`SunFamFlux.not_MW_mgFam`). Because one constant covers the channels
of every dimension, `MW` is a deterministic bound on the flowed origin plaquette at every input
(`BulkBound.facV_le_of_MW`); a π-flux fixed point refutes it at the ray-averaged observer
(`BulkBound.not_MW_blFam`) and at `mgFam` (`SunFamFlux.not_MW_mgFam`).
`SunFamLeak.not_substrateCoreAt_of_plaqLeak` applies at `mgFam` as at any `ConfFlow`.

## 5. What a re-port of the `SU(N)` chain reads of the observer

`ClayNarrow`, `SUNFromScale`, `FlowCovN`, `ApproxJoint`, `ProxyGenLimN` and `GenerationN` read the observer
`sunFam hN2 c hc0 hc s₀` through one lemma, `ObserverFlowSUN.sunFam_physRange` (to build `capData` and `vO`);
`ClassMoments` is derived from the `scale` field at any `W` (`CompositesRenAll.uv_of_scale`,
`ClaySUFinal.classMoments_of_siteExp`). `mgFam_physRange hN2 hc0 hc m hs0 hr.le` has the same conclusion, so
the bundles restated with `mgFam hN2 c hc0 hc m s₀` and the extra witness `m` take it in place of
`sunFam_physRange`; this restatement is not made here. `ConstFlowN` and `ScaleIdentityNoGo` (off the main
chain) also read `sunFam_V_of_lt`, `sunFam_V_of_c_zero` and `eventually_mem_sunFam`; `mgFam_V_of_lt` is the
analogue of the first, the other two are not restated.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the origin, the reflection plane, the lower ends; `1` the unit configuration,
one lattice step, the least stride; `2` the stride ratio between levels, the least colour count; `4` the
dimension; `6 = 3 · 2` the staples; `12` the bound of the block step.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ObserverMultigrid

open MassGap.SUN (SU)
open MassGap.InfiniteLattice MassGap.BlockLattice MassGap.ReflApe MassGap.LatticeReflection
  MassGap.GaugeInvariantAlgebra MassGap.ObserverFlow MassGap.ObserverFlowSUN

/-! ## 1. Sites -/

/-- **The site `x + n ν̂`.** DERIVED: no numeral. -/
def sh (ν : Fin 4) (n : ℤ) (x : ISite) : ISite := Function.update x ν (x ν + n)

/-- DERIVED: no numeral. -/
theorem sh_apply (ν : Fin 4) (n : ℤ) (x : ISite) (i : Fin 4) :
    sh ν n x i = if i = ν then x i + n else x i := by
  unfold sh
  by_cases h : i = ν
  · subst h; simp
  · simp [h]

/-- DERIVED: `1` one lattice step. -/
theorem ishift_apply' (μ : Fin 4) (x : ISite) (i : Fin 4) :
    ishift μ x i = if i = μ then x i + 1 else x i := sh_apply μ 1 x i

/-- DERIVED: no numeral. -/
theorem ireflSite_apply' (τ : Fin 4) (c : ℤ) (x : ISite) (i : Fin 4) :
    ireflSite τ c x i = if i = τ then c - x i else x i := by
  unfold ireflSite
  by_cases h : i = τ
  · subst h; simp
  · simp [h]

/-- Site identities, coordinate by coordinate. -/
macro "site_tac" : tactic => `(tactic| (funext i; simp only [sh_apply, ishift_apply', ireflSite_apply']; split_ifs <;> (first | omega | (subst_vars; simp_all))))

/-- Coordinate bounds `|z j − x j| ≤ d` for a site built from `x` by shifts. -/
macro "dist_tac" : tactic => `(tactic| (intro j; simp only [sh_apply, ishift_apply']; split_ifs <;> rw [abs_le] <;> constructor <;> omega))

/-- DERIVED: `0` the null shift. -/
theorem sh_zero (ν : Fin 4) (x : ISite) : sh ν 0 x = x := by site_tac

/-- DERIVED: no numeral. -/
theorem sh_sh (ν : Fin 4) (a b : ℤ) (x : ISite) : sh ν a (sh ν b x) = sh ν (b + a) x := by site_tac

/-- DERIVED: no numeral. -/
theorem ishift_sh (μ ν : Fin 4) (n : ℤ) (x : ISite) : ishift μ (sh ν n x) = sh ν n (ishift μ x) := by
  site_tac

/-- DERIVED: `1` one lattice step. -/
theorem sh_ishift_nat (ν : Fin 4) (n : ℕ) (x : ISite) :
    sh ν (n : ℤ) (ishift ν x) = sh ν ((n + 1 : ℕ) : ℤ) x := by site_tac

/-- DERIVED: no numeral. -/
theorem refl_sh_ne {τ ν : Fin 4} (h : ν ≠ τ) (c n : ℤ) (x : ISite) :
    ireflSite τ c (sh ν n x) = sh ν n (ireflSite τ c x) := by site_tac

/-- DERIVED: no numeral. -/
theorem refl_sh_eq (τ : Fin 4) (c n : ℤ) (x : ISite) :
    ireflSite τ c (sh τ n x) = sh τ (-n) (ireflSite τ c x) := by site_tac

/-- An alias of `ExistenceFlow.ishift_refl_m1`. -/
alias ishift_reflm1 := MassGap.ExistenceFlow.ishift_refl_m1

/-- An alias of `ExistenceFlow.refl_ishift_tau`. -/
alias refl0_ishift := MassGap.ExistenceFlow.refl_ishift_tau

/-! ## 2. Transporters and strided staples -/

section Paths

variable {G : Type} [Group G]

/-- **The straight transporter** of `n` links from `x` in direction `ν`.
DERIVED: `0` the empty path; `1` one link. -/
def ptr (U : IConf G) (ν : Fin 4) : ℕ → ISite → G
  | 0, _ => 1
  | n + 1, x => U (ν, x) * ptr U ν n (ishift ν x)

/-- DERIVED: `0` the empty path. -/
theorem ptr_zero (U : IConf G) (ν : Fin 4) (x : ISite) : ptr U ν 0 x = 1 := rfl

/-- DERIVED: `1` one link. -/
theorem ptr_succ (U : IConf G) (ν : Fin 4) (n : ℕ) (x : ISite) :
    ptr U ν (n + 1) x = U (ν, x) * ptr U ν n (ishift ν x) := rfl

/-- **The last link of a transporter.** DERIVED: `1` one link. -/
theorem ptr_snoc (U : IConf G) (ν : Fin 4) (n : ℕ) (x : ISite) :
    ptr U ν (n + 1) x = ptr U ν n x * U (ν, sh ν n x) := by
  induction n generalizing x with
  | zero =>
    rw [ptr_succ U ν 0 x, ptr_zero, ptr_zero]
    simp [sh_zero]
  | succ n ih =>
    rw [ptr_succ U ν (n + 1) x, ih (ishift ν x), ptr_succ U ν n x, sh_ishift_nat, mul_assoc]

/-- **A transporter of a gauge transform**: `g(x) · ptr · g(x + nν̂)⁻¹`. DERIVED: no numeral. -/
theorem ptr_gauge (g : ISite → G) (U : IConf G) (ν : Fin 4) (n : ℕ) (x : ISite) :
    ptr (igaugeTransform g U) ν n x = g x * ptr U ν n x * (g (sh ν n x))⁻¹ := by
  induction n generalizing x with
  | zero => simp [ptr_zero, sh_zero]
  | succ n ih =>
    rw [ptr_succ (igaugeTransform g U) ν n x, ptr_succ U ν n x, ih (ishift ν x), sh_ishift_nat]
    simp only [igaugeTransform]
    group

/-- **A transporter reads only its own links.** DERIVED: `0` the first link. -/
theorem ptr_agree (U U' : IConf G) (ν : Fin 4) (n : ℕ) (x : ISite)
    (h : ∀ i : ℕ, i < n → U (ν, sh ν i x) = U' (ν, sh ν i x)) : ptr U ν n x = ptr U' ν n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have h0 : U (ν, x) = U' (ν, x) := by simpa [sh_zero] using h 0 (Nat.succ_pos n)
    have h1 : ptr U ν n (ishift ν x) = ptr U' ν n (ishift ν x) := ih (ishift ν x) (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [← sh_ishift_nat] at this)
    rw [ptr_succ, ptr_succ, h0, h1]

/-- The transporter of the unit configuration is `1`. DERIVED: `1` the unit. -/
theorem ptr_one (ν : Fin 4) (n : ℕ) (x : ISite) : ptr (1 : IConf G) ν n x = 1 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [ptr_succ, ih, Pi.one_apply, one_mul]

/-- **A transporter is continuous in the configuration.** DERIVED: no numeral. -/
theorem continuous_ptr [TopologicalSpace G] [IsTopologicalGroup G] (ν : Fin 4) (n : ℕ) (x : ISite) :
    Continuous (fun U : IConf G => ptr U ν n x) := by
  induction n generalizing x with
  | zero => exact continuous_const
  | succ n ih => exact (continuous_apply (ν, x)).mul (ih (ishift ν x))

/-- A reflected link off the axis. An alias of `ExistenceFlow.conf_refl_ne`. -/
alias reflConf_ne := MassGap.ExistenceFlow.conf_refl_ne

/-- A reflected link on the axis. An alias of `ExistenceFlow.conf_refl_eq`. -/
alias reflConf_eq := MassGap.ExistenceFlow.conf_refl_eq

/-- **A transporter off the axis of the reflection** is the transporter at the reflected site.
DERIVED: `0` the reflection constant. -/
theorem ptr_refl_ne {τ ν : Fin 4} (h : ν ≠ τ) (U : IConf G) (n : ℕ) (x : ISite) :
    ptr (ireflConf τ 0 U) ν n x = ptr U ν n (ireflSite τ 0 x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [ptr_succ, ptr_succ, ih, reflConf_ne h, refl_ishift_ne h]

/-- **A transporter along the axis of the reflection** is the inverse of the transporter that ends at the
reflected site. DERIVED: `0`, `-1` the reflection constants. -/
theorem ptr_refl_eq (τ : Fin 4) (U : IConf G) (n : ℕ) (x : ISite) :
    ptr (ireflConf τ 0 U) τ n x = (ptr U τ n (sh τ (-(n : ℤ)) (ireflSite τ 0 x)))⁻¹ := by
  induction n generalizing x with
  | zero => simp [ptr_zero]
  | succ n ih =>
    have e1 : sh τ (-((n + 1 : ℕ) : ℤ)) (ireflSite τ 0 x)
        = sh τ (-(n : ℤ)) (ireflSite τ 0 (ishift τ x)) := by site_tac
    have e2 : sh τ (n : ℤ) (sh τ (-((n + 1 : ℕ) : ℤ)) (ireflSite τ 0 x)) = ireflSite τ (-1) x := by
      site_tac
    rw [ptr_succ (ireflConf τ 0 U) τ n x, ih, reflConf_eq, ptr_snoc U τ n, e2, mul_inv_rev, e1]

/-- **The stride-`d` staple** beside the link `(μ, x)`: transverse direction `ν = other μ p.1`, side
`p.2`, transverse legs of `d` links each.
DERIVED: `0` names the upper side; `3 = 4 − 1` the directions transverse to `μ`. -/
def stapleD (U : IConf G) (d : ℕ) (μ : Fin 4) (x : ISite) (p : Fin 3 × Fin 2) : G :=
  if p.2 = 0 then
    ptr U (other μ p.1) d x * U (μ, sh (other μ p.1) d x) * (ptr U (other μ p.1) d (ishift μ x))⁻¹
  else
    (ptr U (other μ p.1) d (sh (other μ p.1) (-(d : ℤ)) x))⁻¹ * U (μ, sh (other μ p.1) (-(d : ℤ)) x)
      * ptr U (other μ p.1) d (ishift μ (sh (other μ p.1) (-(d : ℤ)) x))

/-- **A strided staple of a gauge transform.** DERIVED: `0` names the upper side; `3 = 4 − 1` the
directions transverse to `μ`. -/
theorem stapleD_gauge (g : ISite → G) (U : IConf G) (d : ℕ) (μ : Fin 4) (x : ISite)
    (p : Fin 3 × Fin 2) :
    stapleD (igaugeTransform g U) d μ x p = g x * stapleD U d μ x p * (g (ishift μ x))⁻¹ := by
  have e1 : sh (other μ p.1) (d : ℤ) (sh (other μ p.1) (-(d : ℤ)) x) = x := by site_tac
  have e2 : sh (other μ p.1) (d : ℤ) (ishift μ (sh (other μ p.1) (-(d : ℤ)) x)) = ishift μ x := by
    site_tac
  unfold stapleD
  split_ifs
  · rw [ptr_gauge, ptr_gauge]
    simp only [igaugeTransform, ishift_sh]
    group
  · rw [ptr_gauge, ptr_gauge, e1, e2]
    simp only [igaugeTransform]
    group

/-- **A strided staple is continuous in the configuration.** DERIVED: `0` names the upper side;
`3 = 4 − 1` the directions transverse to `μ`. -/
theorem continuous_stapleD [TopologicalSpace G] [IsTopologicalGroup G] (d : ℕ) (μ : Fin 4) (x : ISite)
    (p : Fin 3 × Fin 2) : Continuous (fun U : IConf G => stapleD U d μ x p) := by
  by_cases h : p.2 = 0
  · simp only [stapleD, h, if_true]
    exact ((continuous_ptr _ _ _).mul (continuous_apply _)).mul (continuous_ptr _ _ _).inv
  · simp only [stapleD, h, if_false]
    exact ((continuous_ptr _ _ _).inv.mul (continuous_apply _)).mul (continuous_ptr _ _ _)

/-- **Strided staples of the reflected configuration at a link not along `τ`**: the original staples at
the reflected site, sides swapped for the `τ` direction.
DERIVED: `0` the reflection constant; `0`, `1` name the sides; `3 = 4 − 1` the directions transverse
to `μ`. -/
theorem stapleD_refl_ne {τ μ : Fin 4} (hμ : μ ≠ τ) (U : IConf G) (d : ℕ) (x : ISite)
    (p : Fin 3 × Fin 2) :
    stapleD (ireflConf τ 0 U) d μ x p = stapleD U d μ (ireflSite τ 0 x) (sideSwap μ τ p) := by
  obtain ⟨j, sd⟩ := p
  obtain rfl | rfl : sd = 0 ∨ sd = 1 := by fin_cases sd <;> simp
  · by_cases hν : other μ j = τ
    · simp [stapleD, sideSwap, hν, reflConf_ne hμ, ptr_refl_eq, refl_sh_eq, refl_ishift_ne hμ,
        ishift_sh]
    · simp [stapleD, sideSwap, hν, reflConf_ne hμ, ptr_refl_ne hν, refl_sh_ne hν, refl_ishift_ne hμ]
  · by_cases hν : other μ j = τ
    · simp [stapleD, sideSwap, hν, reflConf_ne hμ, ptr_refl_eq, refl_sh_eq, refl_ishift_ne hμ,
        ishift_sh, sh_sh, sh_zero]
    · simp [stapleD, sideSwap, hν, reflConf_ne hμ, ptr_refl_ne hν, refl_sh_ne hν, refl_ishift_ne hμ,
        ishift_sh]

/-- **Strided staples of the reflected configuration at a `τ`-link**: the inverses of the original
staples at the reflected link, side for side.
DERIVED: `0`, `-1` the reflection constants; `0`, `1` name the sides; `3 = 4 − 1` the directions
transverse to `τ`. -/
theorem stapleD_refl_eq (τ : Fin 4) (U : IConf G) (d : ℕ) (x : ISite) (p : Fin 3 × Fin 2) :
    stapleD (ireflConf τ 0 U) d τ x p = (stapleD U d τ (ireflSite τ (-1) x) p)⁻¹ := by
  obtain ⟨j, sd⟩ := p
  have hν : other τ j ≠ τ := Fin.succAbove_ne τ j
  obtain rfl | rfl : sd = 0 ∨ sd = 1 := by fin_cases sd <;> simp
  · simp [stapleD, reflConf_eq, ptr_refl_ne hν, refl_sh_ne hν, refl0_ishift, ishift_reflm1,
      mul_inv_rev, mul_assoc]
  · simp [stapleD, reflConf_eq, ptr_refl_ne hν, refl_sh_ne hν, refl0_ishift, ishift_reflm1, ishift_sh,
      mul_inv_rev, mul_assoc]

end Paths

/-! ## 3. The strided step and its light cone -/

section Cone

variable {G : Type}

/-- **`F` reads within `R`**: the output of `F` at a link is a function of the input on the links whose
base lies within `R` of the link's base in every coordinate.
DERIVED: no numeral. -/
def ReadsWithin (F : IConf G → IConf G) (R : ℕ) : Prop :=
  ∀ (U U' : IConf G) (l : ILink),
    (∀ l' : ILink, (∀ i, |l'.2 i - l.2 i| ≤ (R : ℤ)) → U l' = U' l') → F U l = F U' l

/-- **Ranges add under composition.** DERIVED: no numeral. -/
theorem ReadsWithin.comp {F H : IConf G → IConf G} {R S : ℕ} (hF : ReadsWithin F R)
    (hH : ReadsWithin H S) : ReadsWithin (H ∘ F) (S + R) := by
  intro U U' l h
  refine hH (F U) (F U') l (fun l' hl' => hF U U' l' (fun l'' hl'' => h l'' (fun i => ?_)))
  have h1 := hl' i
  have h2 := hl'' i
  rw [abs_le] at h1 h2 ⊢
  push_cast
  constructor <;> omega

/-- **`m` iterates read within `m R`.** DERIVED: `0` the empty iterate; `1` one more. -/
theorem ReadsWithin.iterate {F : IConf G → IConf G} {R : ℕ} (hF : ReadsWithin F R) (m : ℕ) :
    ReadsWithin F^[m] (m * R) := by
  induction m with
  | zero => intro U U' l h; exact h l (fun i => by simp)
  | succ m ih =>
    have h := hF.comp ih
    rw [show m * R + R = (m + 1) * R by ring] at h
    exact h

/-- A wider range. DERIVED: no numeral. -/
theorem ReadsWithin.mono {F : IConf G → IConf G} {R R' : ℕ} (hF : ReadsWithin F R) (h : R ≤ R') :
    ReadsWithin F R' :=
  fun U U' l hU => hF U U' l (fun l' hl' => hU l' (fun i => (hl' i).trans (by exact_mod_cast h)))

end Cone

section Step

variable {G : Type} [Group G] [TopologicalSpace G]

/-- **One strided smearing step**: every link replaced by the block step of itself and its six stride-`d`
staples. Applied at every link of `ℤ⁴`.
DERIVED: `6 = 3 · 2` staples. -/
def mgStep (B : BlockStep G) (d : ℕ) (U : IConf G) : IConf G :=
  fun l => B.step (U l) (fun i => stapleD U d l.1 l.2 (finProdFinEquiv.symm i))

/-- **Every link is updated**: no link is held at its input value. DERIVED: no numeral. -/
theorem mgStep_apply (B : BlockStep G) (d : ℕ) (U : IConf G) (l : ILink) :
    mgStep B d U l = B.step (U l) (fun i => stapleD U d l.1 l.2 (finProdFinEquiv.symm i)) := rfl

/-- **The strided step is gauge covariant.** DERIVED: no numeral. -/
theorem mgStep_gauge (B : BlockStep G) (d : ℕ) (g : ISite → G) (U : IConf G) :
    mgStep B d (igaugeTransform g U) = igaugeTransform g (mgStep B d U) := by
  funext l
  obtain ⟨μ, x⟩ := l
  simp only [mgStep]
  have hS : (fun i => stapleD (igaugeTransform g U) d μ x (finProdFinEquiv.symm i))
      = fun i => g x * stapleD U d μ x (finProdFinEquiv.symm i) * (g (ishift μ x))⁻¹ :=
    funext (fun i => stapleD_gauge g U d μ x _)
  rw [hS]
  show B.step (g x * U (μ, x) * (g (ishift μ x))⁻¹) _ = _
  rw [B.gauge]
  rfl

/-- **The strided step is continuous.** DERIVED: no numeral. -/
theorem continuous_mgStep [IsTopologicalGroup G] (B : BlockStep G) (d : ℕ) :
    Continuous (mgStep B d) := by
  refine continuous_pi (fun l => ?_)
  have hs : Continuous (fun U : IConf G => fun i : Fin 6 => stapleD U d l.1 l.2 (finProdFinEquiv.symm i)) :=
    continuous_pi (fun i => continuous_stapleD d l.1 l.2 _)
  exact B.continuous_step.comp ((continuous_apply l).prodMk hs)

/-- **The strided step commutes with the time reflection.**
DERIVED: `0`, `-1` the reflection constants. -/
theorem mgStep_refl (B : BlockStep G) (d : ℕ) (τ : Fin 4) (U : IConf G) :
    mgStep B d (ireflConf τ 0 U) = ireflConf τ 0 (mgStep B d U) := by
  funext l
  obtain ⟨μ, x⟩ := l
  by_cases hμ : μ = τ
  · subst hμ
    have hS : (fun i => stapleD (ireflConf μ 0 U) d μ x (finProdFinEquiv.symm i))
        = fun i => (stapleD U d μ (ireflSite μ (-1) x) (finProdFinEquiv.symm i))⁻¹ :=
      funext (fun i => stapleD_refl_eq μ U d x _)
    have hW : ireflConf μ 0 U (μ, x) = (U (μ, ireflSite μ (-1) x))⁻¹ := reflConf_eq μ U x
    have hR : ireflConf μ 0 (mgStep B d U) (μ, x) = (mgStep B d U (μ, ireflSite μ (-1) x))⁻¹ :=
      reflConf_eq μ _ x
    show B.step (ireflConf μ 0 U (μ, x))
        (fun i => stapleD (ireflConf μ 0 U) d μ x (finProdFinEquiv.symm i)) = _
    rw [hS, hW, hR, B.inv]
    rfl
  · have hS : (fun i => stapleD (ireflConf τ 0 U) d μ x (finProdFinEquiv.symm i))
        = (fun i => stapleD U d μ (ireflSite τ 0 x) (finProdFinEquiv.symm i)) ∘ stapleSwap μ τ := by
      funext i
      simp only [Function.comp, stapleSwap, Equiv.trans_apply, Equiv.symm_apply_apply,
        Function.Involutive.coe_toPerm]
      exact stapleD_refl_ne hμ U d x _
    have hW : ireflConf τ 0 U (μ, x) = U (μ, ireflSite τ 0 x) := reflConf_ne hμ U x
    have hR : ireflConf τ 0 (mgStep B d U) (μ, x) = mgStep B d U (μ, ireflSite τ 0 x) :=
      reflConf_ne hμ _ x
    show B.step (ireflConf τ 0 U (μ, x))
        (fun i => stapleD (ireflConf τ 0 U) d μ x (finProdFinEquiv.symm i)) = _
    rw [hS, hW, hR, B.perm]
    rfl

/-- **The strided step at a link reads only links within `d` of it** (`d ≥ 1`).
DERIVED: `1` the least stride; `0` names the upper side. -/
theorem mgStep_local (B : BlockStep G) {d : ℕ} (hd : 1 ≤ d) (U U' : IConf G) (μ : Fin 4) (x : ISite)
    (h : ∀ (ν : Fin 4) (z : ISite), (∀ i, |z i - x i| ≤ (d : ℤ)) → U (ν, z) = U' (ν, z)) :
    mgStep B d U (μ, x) = mgStep B d U' (μ, x) := by
  have hS : ∀ p, stapleD U d μ x p = stapleD U' d μ x p := by
    intro p
    unfold stapleD
    split_ifs
    · rw [ptr_agree U U' (other μ p.1) d x (fun i hi => h _ _ (by dist_tac)),
        ptr_agree U U' (other μ p.1) d (ishift μ x) (fun i hi => h _ _ (by dist_tac)),
        h μ (sh (other μ p.1) d x) (by dist_tac)]
    · rw [ptr_agree U U' (other μ p.1) d (sh (other μ p.1) (-(d : ℤ)) x)
          (fun i hi => h _ _ (by dist_tac)),
        ptr_agree U U' (other μ p.1) d (ishift μ (sh (other μ p.1) (-(d : ℤ)) x))
          (fun i hi => h _ _ (by dist_tac)),
        h μ (sh (other μ p.1) (-(d : ℤ)) x) (by dist_tac)]
  show B.step (U (μ, x)) _ = B.step (U' (μ, x)) _
  rw [h μ x (fun i => by simp)]
  congr 1
  funext i
  exact hS _

/-- **The strided step reads within `d`.** DERIVED: `1` the least stride. -/
theorem mgStep_reads (B : BlockStep G) {d : ℕ} (hd : 1 ≤ d) : ReadsWithin (mgStep B d) d := by
  intro U U' l h
  obtain ⟨μ, x⟩ := l
  exact mgStep_local B hd U U' μ x (fun ν z hz => h (ν, z) hz)

/-! ## 4. The multigrid map -/

/-- **The multigrid map with `J` levels and `m` steps per level**: `m` strided steps at stride `1`, then
`m` at stride `2`, …, then `m` at stride `2^{J−1}`.
DERIVED: `0` no level; `2` the stride ratio. -/
def mgMap (B : BlockStep G) (m : ℕ) : ℕ → IConf G → IConf G
  | 0 => id
  | J + 1 => (mgStep B (2 ^ J))^[m] ∘ mgMap B m J

/-- **Each level acts on the output of the level below.** DERIVED: `2` the stride ratio. -/
theorem mgMap_succ (B : BlockStep G) (m J : ℕ) :
    mgMap B m (J + 1) = (mgStep B (2 ^ J))^[m] ∘ mgMap B m J := rfl

/-- **The reach of the multigrid map**: `Σ_{j < J} m 2^j`.
DERIVED: `0` no level; `2` the stride ratio. -/
def mgRange (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | J + 1 => m * 2 ^ J + mgRange m J

/-- **The geometric sum**: `mgRange m J + m = m 2^J`. DERIVED: `2` the stride ratio. -/
theorem mgRange_add (m J : ℕ) : mgRange m J + m = m * 2 ^ J := by
  induction J with
  | zero => simp [mgRange]
  | succ J ih =>
    show m * 2 ^ J + mgRange m J + m = m * 2 ^ (J + 1)
    rw [pow_succ, ← mul_assoc, ← ih]
    ring

/-- DERIVED: `2` the stride ratio. -/
theorem mgRange_le (m J : ℕ) : mgRange m J ≤ m * 2 ^ J :=
  (Nat.le_add_right _ m).trans (mgRange_add m J).le

/-- **The multigrid map reads within `mgRange m J`.** DERIVED: `0` no level. -/
theorem mgMap_reads (B : BlockStep G) (m J : ℕ) : ReadsWithin (mgMap B m J) (mgRange m J) := by
  induction J with
  | zero => intro U U' l h; exact h l (fun i => by simp [mgRange])
  | succ J ih => exact ih.comp ((mgStep_reads B Nat.one_le_two_pow).iterate m)

/-- **The multigrid map is gauge covariant.** DERIVED: no numeral. -/
theorem mgMap_gauge (B : BlockStep G) (m J : ℕ) (g : ISite → G) :
    Function.Commute (mgMap B m J) (igaugeTransform g) := by
  induction J with
  | zero => intro U; rfl
  | succ J ih =>
    have hc : Function.Commute (mgStep B (2 ^ J)) (igaugeTransform g) := fun U => mgStep_gauge B _ g U
    exact Function.Commute.comp_left (hc.iterate_left m) ih

/-- **The multigrid map commutes with the time reflection.** DERIVED: `0` the reflection constant. -/
theorem mgMap_refl (B : BlockStep G) (m J : ℕ) (τ : Fin 4) :
    Function.Commute (mgMap B m J) (ireflConf τ 0) := by
  induction J with
  | zero => intro U; rfl
  | succ J ih =>
    have hc : Function.Commute (mgStep B (2 ^ J)) (ireflConf τ 0) := fun U => mgStep_refl B _ τ U
    exact Function.Commute.comp_left (hc.iterate_left m) ih

/-- **The multigrid map is continuous.** DERIVED: no numeral. -/
theorem continuous_mgMap [IsTopologicalGroup G] (B : BlockStep G) (m J : ℕ) :
    Continuous (mgMap B m J) := by
  induction J with
  | zero => exact continuous_id
  | succ J ih => exact ((continuous_mgStep B _).iterate m).comp ih

/-- **Non-degeneracy of a strided step**: a block step that moves some link `W` against six identity
staples moves the configuration equal to `1` off the link `(0, 0)` and to `W` on it, at every stride
`d ≥ 1` (all its stride-`d` staples at `(0, 0)` are `1`).
DERIVED: `0` the origin and direction; `1` the unit configuration and the least stride. -/
theorem mgStep_moves (B : BlockStep G) {d : ℕ} (hd : 1 ≤ d) {W : G}
    (hW : B.step W (fun _ => 1) ≠ W) : ∃ U : IConf G, mgStep B d U ≠ U := by
  classical
  let l0 : ILink := ((0 : Fin 4), (0 : ISite))
  let U0 : IConf G := Function.update (1 : IConf G) l0 W
  have hoff : ∀ l, l ≠ l0 → U0 l = 1 := fun l hl => Function.update_of_ne hl _ _
  have hself : U0 l0 = W := Function.update_self _ _ _
  have hptr : ∀ (ν : Fin 4) (z : ISite), ν ≠ 0 → ptr U0 ν d z = 1 := fun ν z hν =>
    (ptr_agree U0 1 ν d z (fun i _ => hoff _ (fun he => hν (congrArg Prod.fst he)))).trans
      (ptr_one ν d z)
  have hlink : ∀ (ν : Fin 4) (a : ℤ), a ≠ 0 → U0 ((0 : Fin 4), sh ν a 0) = 1 := by
    intro ν a ha
    refine hoff _ (fun he => ha ?_)
    have := congrFun (congrArg Prod.snd he) ν
    simpa [sh_apply, l0] using this
  have hstap : ∀ p, stapleD U0 d 0 0 p = 1 := by
    intro p
    have hν : other 0 p.1 ≠ 0 := Fin.succAbove_ne 0 p.1
    have hd0 : (d : ℤ) ≠ 0 := by omega
    have hd1 : -(d : ℤ) ≠ 0 := by omega
    unfold stapleD
    split_ifs
    · rw [hptr _ _ hν, hptr _ _ hν, hlink _ _ hd0]; simp
    · rw [hptr _ _ hν, hptr _ _ hν, hlink _ _ hd1]; simp
  have hstep : mgStep B d U0 l0 = B.step W (fun _ => 1) := by
    show B.step (U0 l0) (fun i => stapleD U0 d 0 0 (finProdFinEquiv.symm i)) = _
    rw [hself]
    congr 1
    funext i
    exact hstap _
  refine ⟨U0, fun h => hW ?_⟩
  rw [← hstep, h, hself]

end Step

/-! ## 5. The `SU(N)` multigrid observer -/

section SUN

open Matrix
open scoped MatrixOrder ComplexOrder

/-- **The `SU(N)` block step moves a link against six identity staples** (`c > 0`): the link
`diag(i, −i, 1, …, 1)`. The proof of `ObserverFlowSUN.sunStep_moves`, with the staples named.
DERIVED: `2` the least rank; `6` the staple count; `0` the lower end of `c`; `12` as in
`det_blockMatN_mem_slitPlane`. -/
theorem sunStep_moves_one {N : ℕ} (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (hcpos : 0 < c)
    (hc : 12 * c < Real.sin (Real.pi / N)) :
    ∃ W : SU N, sunStep hN c hc0 hc W (fun _ => 1) ≠ W := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  refine ⟨⟨diagonal (witnessVec m), witness_mem m⟩, fun h => ?_⟩
  have hM : projMat (blockMatN c ⟨diagonal (witnessVec m), witness_mem m⟩ (fun _ => 1))
      = diagonal (witnessVec m) := congrArg Subtype.val h
  set X := blockMatN c ⟨diagonal (witnessVec m), witness_mem m⟩ (fun _ => 1) with hXdef
  have hX0 : X.det ≠ 0 :=
    Complex.slitPlane_ne_zero (det_blockMatN_mem_slitPlane hN hc0 hc _ _)
  set d := phase X with hd
  have hdd : star d * d = 1 := star_phase_mul X
  have hU : polar X = star d • diagonal (witnessVec m) := by
    rw [← hM, projMat, smul_smul, ← hd, hdd, one_smul]
  have hP := (polar_spec hX0).2
  rw [hU, conjTranspose_smul, star_star, smul_mul, diagonal_conjTranspose] at hP
  have hentry : ∀ j : Fin (m + 2), (d • (diagonal (star (witnessVec m)) * X)) j j
      = d * (star (witnessVec m j) * (witnessVec m j + 6 * c)) := by
    intro j
    rw [Matrix.smul_apply, diagonal_mul, smul_eq_mul, hXdef]
    congr 2
    simp [blockMatN, Matrix.ofNat_apply, mul_comm]
  have h0 := Complex.nonneg_iff.mp (hP.diag_nonneg (i := 0))
  have h1 := Complex.nonneg_iff.mp (hP.diag_nonneg (i := 1))
  rw [hentry] at h0 h1
  simp [witnessVec, Complex.mul_im, Complex.mul_re] at h0 h1
  have hn : d.re * d.re + d.im * d.im = 1 := by
    have := congrArg Complex.re hdd
    simpa [Complex.mul_re] using this
  have hre : d.re = 0 := by
    have h12 : 12 * c * d.re = 0 := by linarith [h0.2, h1.2]
    rcases mul_eq_zero.mp h12 with h | h
    · linarith
    · exact h
  have him : d.im = 0 := by nlinarith [h0.2, h1.2]
  rw [hre, him] at hn
  norm_num at hn

end SUN

open MassGap.ContinuumFlow MassGap.ContinuumSchwinger Filter

/-- **The multigrid observer as a configuration flow**: `V k = mgMap B m (J k)`, range
`mgRange m (J k)`.
DERIVED: no numeral. -/
def mgConfFlow {N : ℕ} (B : BlockStep (SU N)) (m : ℕ) (J : ℕ → ℕ) : ConfFlow N where
  V k := mgMap B m (J k)
  continuous_V k := continuous_mgMap B m (J k)
  gauge k g U := mgMap_gauge B m (J k) g U
  refl k τ U := mgMap_refl B m (J k) τ U
  range k := mgRange m (J k)
  local_V k l := ⟨baseBox l.2 (mgRange m (J k)), fun l' hl' i => by
      rw [mem_baseBox] at hl'
      have := hl' i
      rw [abs_le]
      constructor <;> omega,
    fun U U' h => mgMap_reads B m (J k) U U' l (fun l' hl' => h l' (by
      rw [mem_baseBox]
      intro i
      have := hl' i
      rw [abs_le] at this
      constructor <;> omega))⟩

/-- **`mgStep (sunBlockStep …) d` moves a configuration** at every stride `d ≥ 1` and `c > 0`.
DERIVED: `1` the least stride; `2` the least rank; `0` the lower end of `c`; `12` as in
`det_blockMatN_mem_slitPlane`. -/
theorem mgStep_sun_moves {N : ℕ} (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (hcpos : 0 < c)
    (hc : 12 * c < Real.sin (Real.pi / N)) {d : ℕ} (hd : 1 ≤ d) :
    ∃ U : Cfg N, mgStep (sunBlockStep hN c hc0 hc) d U ≠ U := by
  obtain ⟨W, hW⟩ := sunStep_moves_one hN hc0 hcpos hc
  exact mgStep_moves (sunBlockStep hN c hc0 hc) hd hW

/-- **The number of levels at step `k`**: `log₂ ⌊s / (m a_k)⌋`.
DERIVED: `2` the stride ratio. -/
def mgLevels (N m : ℕ) (s : ℝ) (k : ℕ) : ℕ := Nat.log 2 ⌊s / ((m : ℝ) * dySpacing N k)⌋₊

/-- **The `SU(N)` multigrid family**: `m` steps of `sunBlockStep` per level, `mgLevels N m s k` levels at
step `k`.
DERIVED: `2` the least rank; `12` as in `det_blockMatN_mem_slitPlane`. -/
def mgFam {N : ℕ} (hN : 2 ≤ N) (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ)
    (s : ℝ) : ConfFlow N :=
  mgConfFlow (sunBlockStep hN c hc0 hc) m (mgLevels N m s)

/-- **The physical reach is at most `s`** at every step: `a_k · mgRange m J_k ≤ s`.
DERIVED: `0` the lower end of `s`; `1` the least `N` of the spacing; `2` the stride ratio. -/
theorem spacing_mul_mgRange_le {N m : ℕ} (hN : 1 ≤ N) {s : ℝ} (hs0 : 0 ≤ s) (k : ℕ) :
    dySpacing N k * (mgRange m (mgLevels N m s k) : ℝ) ≤ s := by
  have ha := dySpacing_pos hN k
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊s / ((m : ℝ) * dySpacing N k)⌋₊ := ⟨_, rfl⟩
  have hJ : mgLevels N m s k = Nat.log 2 n := by rw [hn]; rfl
  by_cases h0 : n = 0
  · rw [hJ, h0, Nat.log_zero_right]
    simpa [mgRange] using hs0
  · have hm : (0 : ℝ) < m := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · exfalso; apply h0; rw [hn, hm]; simp
      · exact_mod_cast hm
    have h1 : (mgRange m (mgLevels N m s k) : ℝ) ≤ m * n := by
      have h2 : mgRange m (mgLevels N m s k) ≤ m * 2 ^ (mgLevels N m s k) := mgRange_le m _
      have h3 : 2 ^ (mgLevels N m s k) ≤ n := by rw [hJ]; exact Nat.pow_log_le_self 2 h0
      exact_mod_cast h2.trans (Nat.mul_le_mul_left m h3)
    have h4 : (n : ℝ) ≤ s / (m * dySpacing N k) := by
      rw [hn]; exact Nat.floor_le (div_nonneg hs0 (mul_nonneg hm.le ha.le))
    have hne : (m : ℝ) * dySpacing N k ≠ 0 := (mul_pos hm ha).ne'
    calc dySpacing N k * (mgRange m (mgLevels N m s k) : ℝ)
        ≤ dySpacing N k * (m * n) := mul_le_mul_of_nonneg_left h1 ha.le
      _ ≤ dySpacing N k * (m * (s / (m * dySpacing N k))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hm.le) ha.le
      _ = s := by field_simp

/-- **`PhysRange r` of the member's observer flow `Φ0` at every `r ≥ s ≥ 0`**, at every step.
DERIVED: `0` the lower end of `s`; `2` the least rank; `12` as in `det_blockMatN_mem_slitPlane`. -/
theorem mgFam_physRange {N : ℕ} (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) {s r : ℝ} (hs0 : 0 ≤ s) (hr : s ≤ r) :
    (MassGap.CompositeLink.Φ0 (mgFam hN c hc0 hc m s)).PhysRange r :=
  Filter.Eventually.of_forall fun k => by
    show dySpacing N k * ((mgRange m (mgLevels N m s k) : ℕ) : ℝ) ≤ r
    exact (spacing_mul_mgRange_le (by omega) hs0 k).trans hr

/-- **At a step with `0 ≤ s < 2 m a_k` the member is the identity** (no level).
DERIVED: `0` no level; `1` the least `N` of the spacing; `2` the least rank and the stride ratio; `12` as
in `det_blockMatN_mem_slitPlane`. -/
theorem mgFam_V_of_lt {N : ℕ} (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) {s : ℝ} {k : ℕ} (hs0 : 0 ≤ s)
    (hs : s < 2 * (m * dySpacing N k)) : (mgFam hN c hc0 hc m s).V k = id := by
  have ha := dySpacing_pos (by omega : 1 ≤ N) k
  have hx : s / ((m : ℝ) * dySpacing N k) < 2 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · exact (div_lt_iff₀ (mul_pos (by exact_mod_cast hm) ha)).2 (by linarith)
  have hfl : ⌊s / ((m : ℝ) * dySpacing N k)⌋₊ < 2 :=
    (Nat.floor_lt (div_nonneg hs0 (mul_nonneg (Nat.cast_nonneg m) ha.le))).2 (by exact_mod_cast hx)
  have hJ : mgLevels N m s k = 0 := Nat.log_eq_zero_iff.2 (Or.inl hfl)
  show mgMap (sunBlockStep hN c hc0 hc) m (mgLevels N m s k) = id
  rw [hJ]
  rfl

open scoped Topology in
/-- **At each fixed step the member is eventually the identity as `s → 0⁺`** (`m ≥ 1`).
DERIVED: `0` the limit; `1` the least `N` and the least `m`; `2` the least rank; `12` as in
`det_blockMatN_mem_slitPlane`. -/
theorem mgFam_eventually_id {N : ℕ} (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    ∀ᶠ s in 𝓝[≥] (0 : ℝ), (mgFam hN c hc0 hc m s).V k = id := by
  have ha := dySpacing_pos (by omega : 1 ≤ N) k
  have hpos : (0 : ℝ) < 2 * (m * dySpacing N k) :=
    mul_pos two_pos (mul_pos (Nat.cast_pos.mpr hm) ha)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds hpos)] with s hs0 hs
  exact mgFam_V_of_lt hN hc0 hc m (Set.mem_Ici.mp hs0) hs

/-- **At `m = 1` and a step with one level the member moves a configuration** (`c > 0`): there
`V k = mgStep (sunBlockStep …) 1`.
DERIVED: `1` the step count, the level count and the stride; `2` the least rank; `0` the lower end of
`c`; `12` as in `det_blockMatN_mem_slitPlane`. -/
theorem mgFam_moves {N : ℕ} (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (hcpos : 0 < c)
    (hc : 12 * c < Real.sin (Real.pi / N)) {s : ℝ} {k : ℕ} (h1 : mgLevels N 1 s k = 1) :
    ∃ U : Cfg N, (mgFam hN c hc0 hc 1 s).V k U ≠ U := by
  obtain ⟨U, hU⟩ := mgStep_sun_moves hN hc0 hcpos hc (le_refl 1)
  refine ⟨U, ?_⟩
  show mgMap (sunBlockStep hN c hc0 hc) 1 (mgLevels N 1 s k) U ≠ U
  rw [h1]
  exact hU

/-! ## 6. The scale input at this observer (stated) -/

section Scale

open MassGap.ClayStatement MassGap.ClayData MassGap.ReflAvg MassGap.MultiScaleAll MassGap.SU2Best

/-- **The observer's moment condition `(M_W)`** (`ScaleSatisfiable` §2): the exponential moments of every
channel of `W` at `s = 1`, `γ = γP = 0`.
DERIVED: `0` the exponents and the lower end of `t`; `1` the scale. -/
def MW {N : ℕ} [NeZero N] (W : ConfFlow N) : Prop :=
  ∃ t C : ℝ, 0 < t ∧ ∀ᶠ k in atTop, ScaleAt (fun _ => W) t C (fun _ => 0) 0 k 1

/-- **`(M_W)` is the scale and top fields at `b = 1`** (`ScaleSatisfiable.scaleControlAll_one_iff`).
DERIVED: `1` the scale. -/
theorem mw_iff {N : ℕ} [NeZero N] (W : ConfFlow N) :
    (∃ Wf : ℝ → ConfFlow N, Wf 1 = W ∧ ScaleControlAll 1 Wf) ↔ MW W :=
  ScaleSatisfiable.scaleControlAll_one_iff W

/-- **The substrate core at the constant family from `(M_W)` and `af`**
(`ScaleSatisfiable.substrateCoreAt_const`).
DERIVED: `1` the scale. -/
theorem substrateCoreAt_of_MW {N : ℕ} [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} (hM : MW W)
    (haf : ∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) z) G ∧ AFCoefficient N G) :
    SubstrateCoreAt W z 1 (fun _ => W) := by
  obtain ⟨t, C, ht, hm⟩ := hM
  exact ScaleSatisfiable.substrateCoreAt_const ht hm haf

end Scale

end MassGap.ObserverMultigrid

end

#print axioms MassGap.ObserverMultigrid.sh_apply
#print axioms MassGap.ObserverMultigrid.ptr_snoc
#print axioms MassGap.ObserverMultigrid.ptr_gauge
#print axioms MassGap.ObserverMultigrid.ptr_agree
#print axioms MassGap.ObserverMultigrid.continuous_ptr
#print axioms MassGap.ObserverMultigrid.ptr_refl_ne
#print axioms MassGap.ObserverMultigrid.ptr_refl_eq
#print axioms MassGap.ObserverMultigrid.stapleD_gauge
#print axioms MassGap.ObserverMultigrid.continuous_stapleD
#print axioms MassGap.ObserverMultigrid.stapleD_refl_ne
#print axioms MassGap.ObserverMultigrid.stapleD_refl_eq
#print axioms MassGap.ObserverMultigrid.ReadsWithin.comp
#print axioms MassGap.ObserverMultigrid.ReadsWithin.iterate
#print axioms MassGap.ObserverMultigrid.mgStep_gauge
#print axioms MassGap.ObserverMultigrid.continuous_mgStep
#print axioms MassGap.ObserverMultigrid.mgStep_refl
#print axioms MassGap.ObserverMultigrid.mgStep_local
#print axioms MassGap.ObserverMultigrid.mgStep_reads
#print axioms MassGap.ObserverMultigrid.mgRange_add
#print axioms MassGap.ObserverMultigrid.mgMap_reads
#print axioms MassGap.ObserverMultigrid.mgMap_gauge
#print axioms MassGap.ObserverMultigrid.mgMap_refl
#print axioms MassGap.ObserverMultigrid.continuous_mgMap
#print axioms MassGap.ObserverMultigrid.mgStep_moves
#print axioms MassGap.ObserverMultigrid.sunStep_moves_one
#print axioms MassGap.ObserverMultigrid.mgConfFlow
#print axioms MassGap.ObserverMultigrid.mgStep_sun_moves
#print axioms MassGap.ObserverMultigrid.spacing_mul_mgRange_le
#print axioms MassGap.ObserverMultigrid.mgFam_physRange
#print axioms MassGap.ObserverMultigrid.mgFam_V_of_lt
#print axioms MassGap.ObserverMultigrid.mgFam_eventually_id
#print axioms MassGap.ObserverMultigrid.mgFam_moves
#print axioms MassGap.ObserverMultigrid.mw_iff
#print axioms MassGap.ObserverMultigrid.substrateCoreAt_of_MW
