import Mathlib
import MassGap.BoxCube
import MassGap.GaugeInvariantAlgebra

/-!
# The connected pairing of a general local observable decays in the infinite-volume state

`GaugeInvariantAlgebra.nu_connected_shift_abs_le` bounds the connected reflected-shifted pairing of a
plaquette in `ν`. This file proves the same for every continuous observable `x` local on a finite set
`S` of links in the positive half `HalfSpaceAlgebra.posHalf τ p`:

    |ν(θx · Sᵐx) − ν(θx) ν(Sᵐx)|  ≤  coreConstG (2 ‖x‖²) 64 β U · coreRate 64 β ^ (m + 2 − U)

for every `m` with `U ≤ m + 2`, where `U` depends on `S` alone (`nu_connected_shift_abs_le_obs`).

The support sits strictly inside a cube based one step below the plane (`exists_cube_posHalf`); its
reflection and its `m`-th translate sit strictly inside two cubes of one larger side whose bases are
`m + R` apart along `τ` (`ireflLink_coord`, `iterate_ishiftLink_coord`), so the two are disjoint and
`BoxCube.stateFree_connected_abs_le_of_cubes` bounds the box pairing once the box holds both cubes,
which happens eventually along `mixCube` (`eventually_cube_mem_iplqAll`).
-/

namespace MassGap.GeneralDecay

open MassGap.ReflectionHalfSpace MassGap.BoxCube

/-! ## Coordinates under the shift and the reflection -/

/-- The `m`-fold shift along `τ` keeps a link's direction and adds `m` to its `τ`-coordinate.

DERIVED: the `4` is the spacetime dimension; the `0` is the unchanged coordinates' increment. -/
theorem iterate_ishiftLink_coord (τ : Fin 4) (m : ℕ) (l : MassGap.InfiniteLattice.ILink) :
    ((MassGap.InfiniteShift.ishiftLink τ)^[m] l).1 = l.1
      ∧ ∀ i : Fin 4, ((MassGap.InfiniteShift.ishiftLink τ)^[m] l).2 i
          = l.2 i + (if i = τ then (m : ℤ) else 0) := by
  induction m with
  | zero => exact ⟨rfl, fun i => by simp⟩
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨ih.1, fun i => ?_⟩
    show (MassGap.GibbsSpec.ishift τ ((MassGap.InfiniteShift.ishiftLink τ)^[m] l).2) i = _
    rw [ishift_coord, ih.2 i]
    by_cases h : i = τ
    · subst h; simp; ring
    · have h' : ¬ τ = i := fun e => h e.symm
      simp [h, h']

#print axioms iterate_ishiftLink_coord

/-- The reflection at `c` keeps a link's direction and every coordinate off `τ`; on `τ` it sends
`y` to `c − y`, or to `c − 1 − y` for a link along `τ`.

DERIVED: the `1` is the one-step offset of a `τ`-link's reflection; the `4` is the dimension. -/
theorem ireflLink_coord (τ : Fin 4) (c : ℤ) (l : MassGap.InfiniteLattice.ILink) :
    (MassGap.LatticeReflection.ireflLink τ c l).1 = l.1
      ∧ ∀ i : Fin 4, (MassGap.LatticeReflection.ireflLink τ c l).2 i
          = if i = τ then (if l.1 = τ then c - 1 - l.2 τ else c - l.2 τ) else l.2 i := by
  refine ⟨rfl, fun i => ?_⟩
  unfold MassGap.LatticeReflection.ireflLink MassGap.LatticeReflection.ireflSite
  by_cases hi : i = τ
  · subst hi; by_cases hl : l.1 = i <;> simp [hl]
  · by_cases hl : l.1 = τ <;> simp [hl, hi, Function.update_of_ne hi]

#print axioms ireflLink_coord

/-! ## Locality of the translate -/

/-- **The `m`-th translate of an observable local on `S` is local on the `m`-fold shifted `S`.**
`InfiniteShift.isLocalOn_ishiftObs` iterated.

DERIVED: the `4` is the spacetime dimension. -/
theorem isLocalOn_iterate_ishiftObsL (τ : Fin 4) {N : ℕ}
    {S : Finset MassGap.InfiniteLattice.ILink}
    (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hx : MassGap.InfiniteLattice.IsLocalOn S (x : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ))
    (m : ℕ) :
    MassGap.InfiniteLattice.IsLocalOn (S.image (MassGap.InfiniteShift.ishiftLink τ)^[m])
      (((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[m] x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
        : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ) := by
  classical
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ', ← Finset.image_image]
    exact MassGap.InfiniteShift.isLocalOn_ishiftObs τ ih

#print axioms isLocalOn_iterate_ishiftObsL

/-- The `m`-th translate does not enlarge the sup norm. `WilsonTransferReduction.norm_ishiftObsL_le`
iterated.

DERIVED: the `4` is the spacetime dimension. -/
theorem norm_iterate_ishiftObsL_le (τ : Fin 4) {N : ℕ}
    (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) (m : ℕ) :
    ‖(⇑(MassGap.ReflectionShift.ishiftObsL τ))^[m] x‖ ≤ ‖x‖ := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact le_trans (MassGap.WilsonTransferReduction.norm_ishiftObsL_le τ _) ih

#print axioms norm_iterate_ishiftObsL_le

/-! ## A cube around a support in the positive half -/

/-- **Every finite link set in the positive half lies strictly inside a cube based one step below the
plane.** Each coordinate of each link is bounded by `M`, the largest coordinate sum; the cube starts at
`p − 1` along `τ` and at `−M − 1` elsewhere, with side `2M + |p| + 1`.

DERIVED: the `1`s are the one step below the plane and the strict-inside margin; `2M` covers the
range `[−M, M]`; the `4` is the dimension. -/
theorem exists_cube_posHalf (τ : Fin 4) (p : ℤ) (S : Finset MassGap.InfiniteLattice.ILink)
    (hS : (S : Set MassGap.InfiniteLattice.ILink) ⊆ MassGap.HalfSpaceAlgebra.posHalf τ p) :
    ∃ (x₀ : MassGap.GibbsSpec.ISite) (R : ℕ), x₀ τ = p - 1 ∧ 1 ≤ R ∧
      ∀ l ∈ S, ∀ i : Fin 4, x₀ i + 1 ≤ l.2 i ∧ l.2 i ≤ x₀ i + R := by
  classical
  let M : ℕ := S.sup (fun l => ∑ i : Fin 4, (l.2 i).natAbs)
  have hM : ∀ l ∈ S, ∀ i : Fin 4, (l.2 i).natAbs ≤ M := by
    intro l hl i
    exact le_trans (Finset.single_le_sum (f := fun j : Fin 4 => (l.2 j).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      (Finset.le_sup (f := fun l : MassGap.InfiniteLattice.ILink => ∑ i : Fin 4, (l.2 i).natAbs) hl)
  refine ⟨fun i => if i = τ then p - 1 else -(M : ℤ) - 1, 2 * M + p.natAbs + 1, by simp, by omega,
    fun l hl i => ?_⟩
  have hb := hM l hl i
  have hτ : p ≤ l.2 τ := hS (Finset.mem_coe.mpr hl)
  have hbτ := hM l hl τ
  by_cases hi : i = τ
  · subst hi; simp only [if_true]; constructor <;> omega
  · simp only [hi, if_false]; constructor <;> omega

#print axioms exists_cube_posHalf

/-! ## The box holds a whole cube eventually -/

open scoped Classical in
/-- The plaquettes of `ℤ⁴` based in the cube of side `R` at `x₀`, as a finite set.

DERIVED: the `4` is the dimension. -/
noncomputable def cubeIPlaq (x₀ : MassGap.GibbsSpec.ISite) (R : ℕ) : Finset MassGap.GibbsSpec.IPlaq :=
  (Finset.univ : Finset (Fin 4 × Fin 4)) ×ˢ
    Fintype.piFinset (fun i : Fin 4 => Finset.Icc (x₀ i) (x₀ i + R))

open scoped Classical in
/-- **Along `mixCube` the box eventually holds every non-degenerate plaquette based in a given cube.**
`ReflectionHalfSpace.mixCube_exhausts` at the finite set of all their links.

DERIVED: the `4` is the dimension. -/
theorem eventually_cube_mem_iplqAll (τ : Fin 4) (p : ℤ) (x₀ : MassGap.GibbsSpec.ISite) (R : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ q : MassGap.GibbsSpec.IPlaq, q.1.1 ≠ q.1.2 → InCube x₀ R q.2 →
      q ∈ iplqAll (mixCube τ p n) := by
  classical
  filter_upwards [mixCube_exhausts τ p
    ((cubeIPlaq x₀ R).biUnion (fun q => (MassGap.GibbsSpec.ilinks q).toFinset))] with n hn q hq hin
  refine mem_iplqAll.mpr ⟨MassGap.GibbsSpec.mem_plaqsIn.mpr (fun l hl => hn ?_), hq⟩
  refine Finset.mem_biUnion.mpr ⟨q, ?_, List.mem_toFinset.mpr hl⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
    Fintype.mem_piFinset.mpr (fun i => Finset.mem_Icc.mpr (hin i))⟩

#print axioms eventually_cube_mem_iplqAll

/-- **`coreConstG` is monotone in its per-term constant**, below the geometric threshold.

DERIVED: the `0` is the sign of the prefactor's other factors; the `1` is the geometric threshold. -/
theorem coreConstG_mono_C {C C' : ℝ} (h : C ≤ C') {K : ℕ} {β : ℝ}
    (hr : MassGap.StrongCoupling.coreRate K β < 1) (u : ℕ) :
    MassGap.StrongCoupling.coreConstG C K β u ≤ MassGap.StrongCoupling.coreConstG C' K β u := by
  unfold MassGap.StrongCoupling.coreConstG MassGap.StrongCoupling.corePrefactorG
  have hd : (0 : ℝ) ≤ (1 - MassGap.StrongCoupling.coreRate K β)⁻¹ := inv_nonneg.mpr (by linarith)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ hd
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (by positivity)) (by positivity)

#print axioms coreConstG_mono_C

/-! ## The pairing bound in the infinite-volume state -/

variable {N : ℕ}

/-- **The connected reflected-shifted pairing of a general local observable decays in `ν`.** Let `ν`
be the `atTop` limit of the free box states along `mixCube`, and `x` continuous and local on a finite
set `S` of links in `posHalf τ p`. There is a `U` depending on `S` alone such that for every `m` with
`U ≤ m + 2`, at `0 ≤ β` with `coreRate 64 β < 1`,

    |ν(θx · Sᵐx) − ν(θx) ν(Sᵐx)|  ≤  coreConstG (2 ‖x‖²) 64 β U · coreRate 64 β ^ (m + 2 − U).

The support lies strictly inside a cube of side `R` based at `p − 1` along `τ`
(`exists_cube_posHalf`). Its reflection at `2p` has `τ`-coordinates in `[p − R, p]` and its `m`-th
translate in `[p + m, p + m + R − 1]` (`ireflLink_coord`, `iterate_ishiftLink_coord`), so both lie
strictly inside cubes of side `R + 1` whose bases are `m + R` apart along `τ`, and the two are disjoint
for `m ≥ 1`. The box state bound is `BoxCube.stateFree_connected_abs_le_of_cubes` at `f = θx`,
`g = Sᵐx`, once the box holds both supports and both cubes, which it does eventually
(`mixCube_exhausts`, `eventually_cube_mem_iplqAll`); along the even boxes it reads as the pairing
`GaugeInvariantAlgebra.pairing_eq_connected`, and `GaugeInvariantAlgebra.nu_pairing_abs_le_of_eventually`
carries it to `ν`. The norms of `θx` and `Sᵐx` are at most `‖x‖`.

DERIVED: `16 * 4` is the box touch-degree bound; `2` in `2 * p` is the reflection plane's doubling and
in `2 ‖x‖²` the two products of `pairTermObs_abs_le`; the `2` in `m + 2` is the two base plaquettes;
`0` is the sign hypotheses and the excluded rank; `1` is the geometric threshold and the identity
boundary configuration. -/
theorem nu_connected_shift_abs_le_obs (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => MassGap.ReflectionHalfSpace.stateFree
          (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β
          (MassGap.ReflectionHalfSpace.mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1)
    (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) {S : Finset MassGap.InfiniteLattice.ILink}
    (hS : (S : Set MassGap.InfiniteLattice.ILink) ⊆ MassGap.HalfSpaceAlgebra.posHalf τ p)
    (hx : MassGap.InfiniteLattice.IsLocalOn S (x : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ)) :
    ∃ U : ℕ, ∀ m : ℕ, U ≤ m + 2 →
      |ν (MassGap.LatticeReflection.ireflObs τ (2 * p) x
            * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[m] x)
        - ν (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
          * ν ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[m] x)|
        ≤ MassGap.StrongCoupling.coreConstG (2 * (‖x‖ * ‖x‖)) (16 * 4) β U
          * MassGap.StrongCoupling.coreRate (16 * 4) β ^ (m + 2 - U) := by
  classical
  obtain ⟨x₀, R, hx₀τ, hR, hin⟩ := exists_cube_posHalf τ p S hS
  refine ⟨32 * (R + 1 + 1) ^ 4, fun m hm => ?_⟩
  -- the two supports and their cubes
  set Sf := S.image (MassGap.LatticeReflection.ireflLink τ (2 * p)) with hSfdef
  set Sg := S.image (MassGap.InfiniteShift.ishiftLink τ)^[m] with hSgdef
  let xr : MassGap.GibbsSpec.ISite := Function.update x₀ τ (p - 1 - R)
  let yr : MassGap.GibbsSpec.ISite := Function.update x₀ τ (p - 1 + m)
  have hpow : 1 ≤ (R + 1 + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hm1 : 1 ≤ m := by omega
  have hcf : ∀ l ∈ Sf, ∀ i : Fin 4, xr i + 1 ≤ l.2 i ∧ l.2 i ≤ xr i + (R + 1 : ℕ) := by
    intro l hl i
    obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.mp hl
    have hc := (ireflLink_coord τ (2 * p) l₀).2 i
    have hb := hin l₀ hl₀ i
    have hbτ := hin l₀ hl₀ τ
    rw [hc]
    by_cases hi : i = τ
    · subst hi
      simp only [xr, Function.update_self, if_true]
      split <;> push_cast <;> constructor <;> omega
    · simp only [xr, Function.update_of_ne hi, hi, if_false]
      push_cast; constructor <;> omega
  have hcg : ∀ l ∈ Sg, ∀ i : Fin 4, yr i + 1 ≤ l.2 i ∧ l.2 i ≤ yr i + (R + 1 : ℕ) := by
    intro l hl i
    obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.mp hl
    have hc := (iterate_ishiftLink_coord τ m l₀).2 i
    have hb := hin l₀ hl₀ i
    rw [hc]
    by_cases hi : i = τ
    · subst hi
      simp only [yr, Function.update_self, if_true]
      push_cast; constructor <;> omega
    · simp only [yr, Function.update_of_ne hi, hi, if_false]
      push_cast; constructor <;> omega
  have hdis : Disjoint Sf Sg := by
    rw [Finset.disjoint_left]
    intro l hlf hlg
    have h1 := (hcf l hlf τ).2
    have h2 := (hcg l hlg τ).1
    simp only [xr, yr, Function.update_self] at h1 h2
    push_cast at h1 h2
    omega
  have hk : m < (yr τ - xr τ).natAbs := by
    simp only [xr, yr, Function.update_self]; omega
  -- locality
  have hfl : MassGap.InfiniteLattice.IsLocalOn Sf
      (MassGap.LatticeReflection.ireflObs τ (2 * p) x : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ) :=
    MassGap.HalfSpaceAlgebra.isLocalOn_ireflObs τ (2 * p) hx
  have hgl := isLocalOn_iterate_ishiftObsL τ x hx m
  -- the box bound, eventually along the even boxes
  have htendS := MassGap.ReflectionHalfSpace.tendsto_symCube_even_of_mixCube τ p hN β ν htend
  have hdouble : Filter.Tendsto (fun j : ℕ => 2 * j) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      Sf ⊆ mixCube τ p n ∧ Sg ⊆ mixCube τ p n
      ∧ (∀ q : MassGap.GibbsSpec.IPlaq, q.1.1 ≠ q.1.2 → InCube xr (R + 1) q.2 →
          q ∈ iplqAll (mixCube τ p n))
      ∧ (∀ q : MassGap.GibbsSpec.IPlaq, q.1.1 ≠ q.1.2 → InCube yr (R + 1) q.2 →
          q ∈ iplqAll (mixCube τ p n)) :=
    (mixCube_exhausts τ p Sf).and ((mixCube_exhausts τ p Sg).and
      ((eventually_cube_mem_iplqAll τ p xr (R + 1)).and (eventually_cube_mem_iplqAll τ p yr (R + 1))))
  have hr0 : 0 ≤ MassGap.StrongCoupling.coreRate (16 * 4) β :=
    MassGap.StrongCoupling.coreRate_nonneg _ hβ
  refine MassGap.GaugeInvariantAlgebra.nu_pairing_abs_le_of_eventually (l := Filter.atTop)
    (fun n => MassGap.ReflectionHalfSpace.stateFree (φ := MassGap.WilsonAction.wilsonDensity)
      MassGap.WilsonAction.measurable_wilsonDensity
      (MassGap.WilsonAction.wilsonDensity_nonneg hN)
      (MassGap.WilsonAction.wilsonDensity_le_two hN) β
      (MassGap.ReflectionHalfSpace.symCube τ (2 * p) n) 1)
    ν htendS τ (2 * p) x ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[m] x) _ ?_
  filter_upwards [hdouble.eventually hev] with n hn
  simp only [mixCube_even] at hn
  obtain ⟨h1, h2, h3, h4⟩ := hn
  rw [MassGap.GaugeInvariantAlgebra.pairing_eq_connected]
  have hbox := stateFree_connected_abs_le_of_cubes hN
    (MassGap.WilsonAction.wilsonDensity_nonneg hN) (MassGap.WilsonAction.wilsonDensity_le_two hN) hβ
    (symCube τ (2 * p) n) 1
    (MassGap.LatticeReflection.ireflObs τ (2 * p) x) ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[m] x)
    h1 h2 hfl hgl hdis hcf hcg h3 h4 hr τ m hk hm
  refine le_trans hbox (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr0 _))
  refine coreConstG_mono_C ?_ hr _
  have hf := MassGap.WilsonTransferReduction.norm_ireflObs_le τ (2 * p) x
  have hg := norm_iterate_ishiftObsL_le τ x m
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg _
  have := mul_le_mul hf hg (norm_nonneg _) hx0
  linarith

#print axioms nu_connected_shift_abs_le_obs

end MassGap.GeneralDecay
