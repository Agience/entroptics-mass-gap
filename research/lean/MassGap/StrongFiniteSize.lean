import Mathlib
import MassGap.StrongKernelNear
import MassGap.FlowComp

/-!
# MassGap.StrongFiniteSize — the finite-size effect of the torus energy reading vanishes exponentially at strong coupling

At `|β| ≤ β₀ = 2^{-16}`, every `N ≠ 0` and every side `n`, the plaquette energy reading of the periodic torus
state, `ObserverFlowSeed.bareRead hN n β`, moves by at most `1024 · e^{−(log 2 / 2) n}` when the side doubles.
The integrated doubling change `∫₀^β bareDelta = defectW N β n` is then at most `β · 16 n⁴ · 1024 e^{−(log 2/2) n}`
on `[0, β₀]`, and this bound tends to `0` as `n` grows.

## The mechanism: box conditioning, not a torus cluster expansion

1. **Torus DLR** (`PeriodicStateDLR.torusState_dlr`). The torus state of extent `M + 1` reads a local observable
   `F` as it reads the box kernel `wspec Δ F` (the infinite-lattice Wilson specification on `Δ` with boundary
   condition), once reduction modulo `M + 1` is injective on `F`'s support, `Δ`, and the links and plaquettes
   touching `Δ`.
2. **Boundary-condition independence** (`StrongKernelNear.kernelNear_strong_explicit`). At `|β| ≤ 2^{-16}`
   the box kernel of `F` (`|F| ≤ 1`, support `A ⊆ Δ`) lies within `δ = 2 |A| 2^{−L}` of one constant `c` at
   every boundary condition, `L` the depth of `A` in `Δ` (Dobrushin's single-link sweep on the real Wilson
   specification).
3. **Two tori, one constant** (`torusState_sub_le`). Both torus states of sides `M + 1` and `M' + 1` read
   `F` within `δ` of the same `c`, since a state averages a function lying in `[c − δ, c + δ]`. So
   `|ν_M F − ν_{M'} F| ≤ 2δ`. A finite-size effect is the dependence of the box kernel on the wrap-around part
   of the boundary condition; step 2 makes that dependence `O(2^{−L})` uniformly.

## The geometry (proved)

* `snorm x = maxᵢ |xᵢ|`; `box R` the links based in `[−R, R]⁴`; `depth R l = R + 1 − snorm l.2`.
* `depth` vanishes off `box R` and drops by at most `1` along `StrongKernelNear.nbr` (`snorm_nbr`: a link and a
  link of a plaquette through it have bases within sup-distance `1`).
* `bplaq_coord`, `bdLinks_coord`: the plaquettes touching `box R` and their links are based in `[−R−1, R+1]⁴`,
  so `linkMod M`, `plaqMod M` are injective there at `2 (R + 1) < M + 1` (`linkMod_injOn`, `plaqMod_injOn`).

## The results (proved)

* **`torusState_sub_le`** (any local observable): `|F| ≤ 1`, `F` local on `A`, every link of `A` based within
  sup-distance `s ≤ R` of the origin, `2 (R + 1) < M + 1, M' + 1`:
  `|torusState hN M β F − torusState hN M' β F| ≤ 4 |A| 2^{−(R + 1 − s)}`.
* `plaq_sub_le`: the plaquette density at the origin, `16 · 2^{−R}` (`s = 1`, `|A| ≤ 4`, via `F = φ − 1`).
* `bareRead_sub_le`: `|bareRead (2n) − bareRead n| ≤ 256 · 2^{−R}` at `1 ≤ R`, `2 (R + 1) < n`;
  `finiteSize_decay_strong_pow`: `≤ 256 · 2^{−⌊(n−3)/2⌋}` at `n ≥ 5`.
* **`finiteSize_decay_strong`**: `|bareRead hN (2n) β − bareRead hN n β| ≤ 1024 · e^{−(log 2/2) n}` for every `n`,
  every `N ≠ 0`, every `|β| ≤ 2^{-16}` (`n ≤ 4` from `abs_bareRead_le`: `|bareRead| ≤ 32`).
* `abs_bareDelta_le`, **`integral_bareDelta_strong_le`**: `|bareDelta hN n x| ≤ 16 n⁴ · 1024 e^{−(log 2/2) n}` on
  `|x| ≤ 2^{-16}`, so `|∫₀^β bareDelta hN n| ≤ β · 16 n⁴ · 1024 e^{−(log 2/2) n}` for `0 ≤ β ≤ 2^{-16}`.
* **`abs_defectW_strong_le`**: the same bound on `|defectW N β n|` at `n ≠ 0` (`FlowComp.integral_bareDelta`).
* `tendsto_strongBound`: `16 n⁴ · 1024 e^{−(log 2/2) n} → 0`; `defectW_strong_eventually`: for every `η > 0`, all
  large `n` have `|defectW N β n| ≤ η` at every `β ∈ [0, 2^{-16}]`.

## Relation to `FlowComp` §2

`FlowComp.flowEnergyComp_of_split` asks for the strong part `defectW N x₀ n − K · flowDefect hN W (κ β) n x₀ ≤ η₁`
eventually in `β` at the window side. At `x₀ = 2^{-16}` the bare term is `abs_defectW_strong_le`: it is below any
`η₁ > 0` once the side passes the threshold of `defectW_strong_eventually`. The flowed term
`K · flowDefect hN W k n x₀` is the integral of the doubling change of the flowed reading; `torusState_sub_le`
bounds it in absolute value in the same way once each flowed plaquette density `W.fieldMap k (plaqField (p, 0))`
is local on a link set of sup-radius `s`, with `s` fixed (or `s = o(n)`) as `n` grows and `2 (s + 1) < n`, at the
rate `2^{−(R + 1 − s)}`. `ConfFlow`'s locality field `local_V` gives `s = W.range k + 1`; that step and the
passage from "large side" to "eventually in `β`" (the window side grows with `β`, `n > C / (2 aRun N β)` with
`aRun N β → 0`) are in `StrongLocalFiniteSize`.

DERIVED (module-wide): `4` the dimension and the links of a plaquette; `16 = 4 · 4` the ordered planes and
`2 · 2 · 4`; `256 = 16 · 16`; `1024 = 256 · 2²`; `32 = 16 · 2` the bound of `bareRead`; `65536 = 2^{16}` the
strong-coupling threshold of `StrongKernelNear`; `1/2` its contraction rate; `2` the doubling, the range of the
plaquette density and the two tori; `1` the unit step and the plaquette's sup-radius; `3`, `5` the least side
with `1 ≤ ⌊(n − 3)/2⌋`; `0` the origin.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.StrongFiniteSize

open Filter Topology
open MassGap.GibbsSpec
open MassGap.StrongKernelNear (IsLocalOn nbr kernelNear_strong_explicit)
open MassGap.PeriodicState (torusState)
open MassGap.PeriodicStateDLR (wspec torusState_dlr finMod_inj_of_abs_le)
open MassGap.InfiniteLattice (linkMod plaqMod)
open MassGap.ObserverFlowSeed (bareRead bareDelta)
open MassGap.ObserverEnergyMoments (plaqField)
open MassGap.WilsonAction (wilsonDensity wilsonDensity_nonneg wilsonDensity_le_two)

variable {N : ℕ}

/-! ## 1. Geometry of the box -/

/-- The sup-norm of a site. DERIVED: `4` the dimension. -/
def snorm (x : ISite) : ℕ := Finset.univ.sup fun i : Fin 4 => (x i).natAbs

/-- DERIVED: no numeral. -/
theorem natAbs_le_iff' {a : ℤ} {k : ℕ} : a.natAbs ≤ k ↔ -(k : ℤ) ≤ a ∧ a ≤ k := by
  rcases Int.natAbs_eq a with h | h <;> constructor <;> intro h' <;> omega

/-- DERIVED: `4` the dimension. -/
theorem snorm_le_iff {x : ISite} {k : ℕ} : snorm x ≤ k ↔ ∀ i, -(k : ℤ) ≤ x i ∧ x i ≤ k := by
  unfold snorm
  rw [Finset.sup_le_iff]
  simp only [Finset.mem_univ, true_implies, natAbs_le_iff']

/-- The links based in `[−R, R]⁴`. DERIVED: `4` the dimension. -/
def box (R : ℕ) : Finset ILink :=
  (Finset.univ : Finset (Fin 4)) ×ˢ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(R : ℤ)) R)

/-- DERIVED: no numeral. -/
theorem mem_box {R : ℕ} {l : ILink} : l ∈ box R ↔ snorm l.2 ≤ R := by
  rw [snorm_le_iff]
  simp only [box, Finset.mem_product, Finset.mem_univ, true_and, Fintype.mem_piFinset, Finset.mem_Icc]

/-- DERIVED: no numeral. -/
theorem box_coord {R : ℕ} {l : ILink} (hl : l ∈ box R) (i : Fin 4) : -(R : ℤ) ≤ l.2 i ∧ l.2 i ≤ R :=
  snorm_le_iff.mp (mem_box.mp hl) i

/-- A unit step moves one coordinate by `0` or `1`. DERIVED: `1` the unit step. -/
theorem ishift_bounds (a : Fin 4) (x : ISite) (i : Fin 4) :
    x i ≤ ishift a x i ∧ ishift a x i ≤ x i + 1 := by
  unfold ishift
  by_cases h : i = a
  · subst h
    rw [Function.update_self]
    omega
  · rw [Function.update_of_ne h]
    omega

/-- The links of a plaquette are based at its base or one unit step from it. DERIVED: `1` the unit step. -/
theorem ilinks_base {q : IPlaq} {l : ILink} (hl : l ∈ ilinks q) (i : Fin 4) :
    q.2 i ≤ l.2 i ∧ l.2 i ≤ q.2 i + 1 := by
  rw [ilinks_eq] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · exact ⟨le_rfl, le_add_of_nonneg_right zero_le_one⟩
  · exact ishift_bounds q.1.1 q.2 i
  · exact ishift_bounds q.1.2 q.2 i
  · exact ⟨le_rfl, le_add_of_nonneg_right zero_le_one⟩

/-- A link and a link of a plaquette through it are based within sup-distance `1`.
DERIVED: `1` the unit step. -/
theorem snorm_nbr {i j : ILink} (h : j ∈ nbr i) : snorm j.2 ≤ snorm i.2 + 1 := by
  unfold nbr at h
  obtain ⟨q, hq, hj⟩ := Finset.mem_biUnion.mp h
  obtain ⟨l, hl, hli⟩ := mem_boundaryPlaqs.mp hq
  rw [Finset.mem_singleton] at hli
  rw [hli] at hl
  have hj' := List.mem_toFinset.mp hj
  rw [snorm_le_iff]
  intro c
  have h1 := ilinks_base hl c
  have h2 := ilinks_base hj' c
  have h3 := (snorm_le_iff.mp (le_refl (snorm i.2))) c
  push_cast
  omega

/-- The plaquettes touching `box R` are based in `[−R−1, R]⁴`. DERIVED: `1` the unit step. -/
theorem bplaq_coord {R : ℕ} {q : IPlaq} (hq : q ∈ boundaryPlaqs (box R)) (i : Fin 4) :
    -((R : ℤ) + 1) ≤ q.2 i ∧ q.2 i ≤ R := by
  obtain ⟨l, hl, hlb⟩ := mem_boundaryPlaqs.mp hq
  have h1 := box_coord hlb i
  have h2 := ilinks_base hl i
  omega

/-- The links of the plaquettes touching `box R` are based in `[−R−1, R+1]⁴`. DERIVED: `1` the unit step. -/
theorem bdLinks_coord {R : ℕ} {l : ILink} (hl : l ∈ MassGap.WilsonDLR.bdLinks (box R)) (i : Fin 4) :
    -((R : ℤ) + 1) ≤ l.2 i ∧ l.2 i ≤ R + 1 := by
  unfold MassGap.WilsonDLR.bdLinks at hl
  obtain ⟨q, hq, hlq⟩ := Finset.mem_biUnion.mp hl
  have h1 := bplaq_coord hq i
  have h2 := ilinks_base (List.mem_toFinset.mp hlq) i
  omega

/-- Reduction modulo `M + 1 > 2B` is injective on links based in `[−B, B]⁴`. DERIVED: `2` the two sides. -/
theorem linkMod_injOn {M B : ℕ} (hB : 2 * B < M + 1) {T : Finset ILink}
    (hT : ∀ l ∈ T, ∀ i, -(B : ℤ) ≤ l.2 i ∧ l.2 i ≤ B) :
    Set.InjOn (linkMod M) (T : Set ILink) := by
  intro l hl l' hl' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext h1 (funext fun i => finMod_inj_of_abs_le hB
    (abs_le.mpr (hT l (Finset.mem_coe.mp hl) i)) (abs_le.mpr (hT l' (Finset.mem_coe.mp hl') i))
    (congrFun h2 i))

/-- Reduction modulo `M + 1 > 2B` is injective on plaquettes based in `[−B, B]⁴`. DERIVED: `2` the two
sides. -/
theorem plaqMod_injOn {M B : ℕ} (hB : 2 * B < M + 1) {Q : Finset IPlaq}
    (hQ : ∀ q ∈ Q, ∀ i, -(B : ℤ) ≤ q.2 i ∧ q.2 i ≤ B) :
    Set.InjOn (plaqMod M) (Q : Set IPlaq) := by
  intro q hq q' hq' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext h1 (funext fun i => finMod_inj_of_abs_le hB
    (abs_le.mpr (hQ q (Finset.mem_coe.mp hq) i)) (abs_le.mpr (hQ q' (Finset.mem_coe.mp hq') i))
    (congrFun h2 i))

/-- The depth of a link in `box R`: `R + 1 − snorm`, `0` off the box. DERIVED: `1` the unit step. -/
def depth (R : ℕ) (l : ILink) : ℕ := R + 1 - snorm l.2

/-- The depth drops by at most `1` between sites within sup-distance `1`. DERIVED: `1` the unit step. -/
theorem depth_le_succ {R : ℕ} {i j : ILink} (h : snorm j.2 ≤ snorm i.2 + 1) :
    depth R i ≤ depth R j + 1 := by
  unfold depth
  omega

/-! ## 2. Two tori read a local observable alike -/

/-- **Two torus states agree on a local observable up to `4 |A| 2^{−(R+1−s)}`** at `|β| ≤ 2^{-16}`, once both
extents exceed `2 (R + 1)`. DERIVED: `4 = 2 · 2` the two tori and the kernel bound's `2`; `65536 = 2^{16}`;
`1/2` the contraction rate; `2` the two sides. -/
theorem torusState_sub_le (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) {R s M M' : ℕ}
    (F : C(IConf (MassGap.SUN.SU N), ℝ)) (A : Finset ILink) (hF1 : ∀ ω, |F ω| ≤ 1)
    (hloc : IsLocalOn A ⇑F) (hA : ∀ l ∈ A, snorm l.2 ≤ s) (hsR : s ≤ R)
    (hM : 2 * (R + 1) < M + 1) (hM' : 2 * (R + 1) < M' + 1) :
    |torusState hN M β F - torusState hN M' β F| ≤ 4 * A.card * (1 / 2) ^ (R + 1 - s) := by
  have hAΔ : A ⊆ box R := fun l hl => mem_box.mpr ((hA l hl).trans hsR)
  obtain ⟨c, hc⟩ := kernelNear_strong_explicit hN hβ (box R) A hAΔ F hF1 hloc (depth R)
    (fun l hl => by
      have := mt mem_box.mpr hl
      unfold depth
      omega)
    (fun _ _ _ hj => depth_le_succ (snorm_nbr hj))
    (R + 1 - s) (fun l hl => by
      have := hA l hl
      unfold depth
      omega)
  have hδ0 : 0 ≤ 2 * (A.card : ℝ) * (1 / 2) ^ (R + 1 - s) := by positivity
  have key : ∀ K : ℕ, 2 * (R + 1) < K + 1 →
      |torusState hN K β F - c| ≤ 2 * (A.card : ℝ) * (1 / 2) ^ (R + 1 - s) := by
    intro K hK
    have hT : ∀ l ∈ A ∪ box R ∪ MassGap.WilsonDLR.bdLinks (box R), ∀ i,
        -((R + 1 : ℕ) : ℤ) ≤ l.2 i ∧ l.2 i ≤ ((R + 1 : ℕ) : ℤ) := by
      intro l hl i
      push_cast
      rcases Finset.mem_union.mp hl with h | h
      · rcases Finset.mem_union.mp h with h | h
        · have := box_coord (hAΔ h) i
          omega
        · have := box_coord h i
          omega
      · exact bdLinks_coord h i
    have hP : ∀ q ∈ boundaryPlaqs (box R), ∀ i,
        -((R + 1 : ℕ) : ℤ) ≤ q.2 i ∧ q.2 i ≤ ((R + 1 : ℕ) : ℤ) := by
      intro q hq i
      push_cast
      have := bplaq_coord hq i
      omega
    have hdlr := torusState_dlr hN K β (box R) A F (fun U V h => hloc U V h)
      (linkMod_injOn hK hT) (plaqMod_injOn hK hP)
    have hone : torusState hN K β (c • (1 : C(IConf (MassGap.SUN.SU N), ℝ))) = c := by
      rw [MassGap.DLRLimit.State.map_smul, MassGap.DLRLimit.State.map_one, mul_one]
    rw [← hdlr]
    calc |torusState hN K β (wspec hN β (box R) F) - c|
        = |torusState hN K β (wspec hN β (box R) F)
            - torusState hN K β (c • (1 : C(IConf (MassGap.SUN.SU N), ℝ)))| := by rw [hone]
      _ ≤ ‖wspec hN β (box R) F - c • (1 : C(IConf (MassGap.SUN.SU N), ℝ))‖ :=
          (torusState hN K β).abs_sub_le _ _
      _ ≤ 2 * (A.card : ℝ) * (1 / 2) ^ (R + 1 - s) :=
          (ContinuousMap.norm_le _ hδ0).mpr fun ω => by
            rw [Real.norm_eq_abs, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
              ContinuousMap.one_apply, smul_eq_mul, mul_one]
            exact hc ω
  have h1 := key M hM
  have h2 := key M' hM'
  have h3 := abs_sub_le (torusState hN M β F) c (torusState hN M' β F)
  rw [abs_sub_comm c] at h3
  linarith

/-! ## 3. The plaquette energy reading -/

/-- The plaquette density at the origin, shifted to `[−1, 1]`. DERIVED: `1` the centre of `[0, 2]`;
`0` the origin. -/
def plaqDev (p : Fin 4 × Fin 4) : C(IConf (MassGap.SUN.SU N), ℝ) :=
  (plaqField (N := N) (p, 0)).1 - 1

/-- DERIVED: `1` the centre; `0` the origin. -/
theorem plaqDev_apply (p : Fin 4 × Fin 4) (ω : IConf (MassGap.SUN.SU N)) :
    plaqDev (N := N) p ω = wilsonDensity (ihol (p, 0) ω) - 1 := rfl

/-- **Two torus states agree on the plaquette density at the origin up to `16 · 2^{−R}`.** DERIVED:
`16 = 4 · 4` (`4` from `torusState_sub_le`, `4` the links of a plaquette); `1` the plaquette's sup-radius;
`65536 = 2^{16}` the strong-coupling threshold of `StrongKernelNear`. -/
theorem plaq_sub_le (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) {R M M' : ℕ} (hR : 1 ≤ R)
    (hM : 2 * (R + 1) < M + 1) (hM' : 2 * (R + 1) < M' + 1) (p : Fin 4 × Fin 4) :
    |torusState hN M β (plaqField (N := N) (p, 0)).1 - torusState hN M' β (plaqField (N := N) (p, 0)).1|
      ≤ 16 * (1 / 2) ^ R := by
  have hF1 : ∀ ω, |plaqDev (N := N) p ω| ≤ 1 := fun ω => by
    rw [plaqDev_apply]
    have h0 := wilsonDensity_nonneg hN (ihol (p, 0) ω)
    have h2 := wilsonDensity_le_two hN (ihol (p, 0) ω)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hloc : IsLocalOn (ilinks (p, (0 : ISite))).toFinset ⇑(plaqDev (N := N) p) := fun η η' h => by
    rw [plaqDev_apply, plaqDev_apply,
      ihol_congr (p, 0) η η' (fun l hl => h l (List.mem_toFinset.mpr hl))]
  have hA : ∀ l ∈ (ilinks (p, (0 : ISite))).toFinset, snorm l.2 ≤ 1 := fun l hl => by
    rw [snorm_le_iff]
    intro i
    have := ilinks_base (List.mem_toFinset.mp hl) i
    dsimp only [Pi.zero_apply] at this
    push_cast
    omega
  have hcard : ((ilinks (p, (0 : ISite))).toFinset.card : ℝ) ≤ 4 := by
    have : (ilinks (p, (0 : ISite))).toFinset.card ≤ 4 := (List.toFinset_card_le _).trans le_rfl
    exact_mod_cast this
  have h := torusState_sub_le hN hβ (plaqDev (N := N) p) _ hF1 hloc hA hR hM hM'
  rw [plaqDev, MassGap.DLRLimit.State.map_sub, MassGap.DLRLimit.State.map_sub,
    MassGap.DLRLimit.State.map_one, MassGap.DLRLimit.State.map_one, Nat.add_sub_cancel] at h
  have he : ∀ a b : ℝ, a - 1 - (b - 1) = a - b := fun a b => by ring
  rw [he] at h
  have hp : (0 : ℝ) ≤ (1 / 2) ^ R := by positivity
  calc _ ≤ 4 * ((ilinks (p, (0 : ISite))).toFinset.card : ℝ) * (1 / 2) ^ R := h
    _ ≤ 4 * 4 * (1 / 2) ^ R := by gcongr
    _ = 16 * (1 / 2) ^ R := by norm_num

/-- **The doubling change of the torus energy reading at strong coupling**: `≤ 256 · 2^{−R}` once
`1 ≤ R` and `2 (R + 1) < n`. DERIVED: `256 = 16 · 16` the ordered planes times `plaq_sub_le`; `2` the
doubling; `65536 = 2^{16}` the strong-coupling threshold of `StrongKernelNear`. -/
theorem bareRead_sub_le (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) {n R : ℕ} (hR : 1 ≤ R)
    (hn : 2 * (R + 1) < n) :
    |bareRead hN (2 * n) β - bareRead hN n β| ≤ 256 * (1 / 2) ^ R := by
  unfold bareRead
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ p : Fin 4 × Fin 4, |torusState hN (2 * n - 1) β (plaqField (N := N) (p, 0)).1
          - torusState hN (n - 1) β (plaqField (N := N) (p, 0)).1| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Fin 4 × Fin 4, 16 * (1 / 2 : ℝ) ^ R :=
        Finset.sum_le_sum fun p _ => plaq_sub_le hN hβ hR (by omega) (by omega) p
    _ = 256 * (1 / 2) ^ R := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        norm_num
        ring

/-- At `n ≥ 5`, with `R = ⌊(n − 3)/2⌋`. DERIVED: `3`, `5` the least side with `1 ≤ R`; `256` from
`bareRead_sub_le`; `65536 = 2^{16}` the strong-coupling threshold of `StrongKernelNear`. -/
theorem finiteSize_decay_strong_pow (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) {n : ℕ} (hn : 5 ≤ n) :
    |bareRead hN (2 * n) β - bareRead hN n β| ≤ 256 * (1 / 2) ^ ((n - 3) / 2) :=
  bareRead_sub_le hN hβ (by omega) (by omega)

/-- `|bareRead| ≤ 32`: sixteen readings of a density in `[0, 2]`. DERIVED: `32 = 16 · 2`. -/
theorem abs_bareRead_le (hN : N ≠ 0) (n : ℕ) (β : ℝ) : |bareRead hN n β| ≤ 32 := by
  unfold bareRead
  calc _ ≤ ∑ p : Fin 4 × Fin 4, |torusState hN (n - 1) β (plaqField (N := N) (p, 0)).1| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Fin 4 × Fin 4, (2 : ℝ) := Finset.sum_le_sum fun p _ =>
        ((torusState hN (n - 1) β).abs_le_norm _).trans
          ((ContinuousMap.norm_le _ (by norm_num)).mpr fun ω => by
            rw [Real.norm_eq_abs]
            show |wilsonDensity (ihol (p, 0) ω)| ≤ 2
            exact abs_le.mpr ⟨by linarith [wilsonDensity_nonneg hN (ihol (p, 0) ω)],
              wilsonDensity_le_two hN (ihol (p, 0) ω)⟩)
    _ = 32 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        norm_num

/-- `e^{(log 2 / 2) n} ≤ 2^k` at `n ≤ 2k`. DERIVED: `2` the base and the halving. -/
theorem exp_half_le {n k : ℕ} (h : n ≤ 2 * k) : Real.exp (Real.log 2 / 2 * n) ≤ 2 ^ k := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hnk : (n : ℝ) ≤ 2 * k := by exact_mod_cast h
  have h1 : Real.log 2 / 2 * n ≤ k * Real.log 2 := by nlinarith
  calc Real.exp (Real.log 2 / 2 * n) ≤ Real.exp (k * Real.log 2) := Real.exp_le_exp.mpr h1
    _ = 2 ^ k := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- **The finite-size effect of the torus energy reading vanishes exponentially at strong coupling.**
For every `N ≠ 0`, every `|β| ≤ 2^{-16}` and every side `n`:
`|bareRead hN (2n) β − bareRead hN n β| ≤ 1024 · e^{−(log 2 / 2) n}`.
DERIVED: `1024 = 256 · 2²`; `log 2 / 2` the rate `2^{−R}` at `R ≈ n/2`; `65536 = 2^{16}`; `5` the least side of
`finiteSize_decay_strong_pow`; `64 = 2 · 32 ≤ 256`. -/
theorem finiteSize_decay_strong (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) (n : ℕ) :
    |bareRead hN (2 * n) β - bareRead hN n β| ≤ 1024 * Real.exp (-(Real.log 2 / 2) * n) := by
  have hE : 0 < Real.exp (Real.log 2 / 2 * n) := Real.exp_pos _
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv]
  by_cases hn : 5 ≤ n
  · have h1 := finiteSize_decay_strong_pow hN hβ hn
    have h2 := exp_half_le (n := n) (k := (n - 3) / 2 + 2) (by omega)
    have h3 : (256 : ℝ) * (1 / 2) ^ ((n - 3) / 2) = 1024 / 2 ^ ((n - 3) / 2 + 2) := by
      rw [pow_add, one_div_pow]
      field_simp
      norm_num
    calc _ ≤ 1024 / (2 : ℝ) ^ ((n - 3) / 2 + 2) := h1.trans h3.le
      _ ≤ 1024 / Real.exp (Real.log 2 / 2 * n) := div_le_div_of_nonneg_left (by norm_num) hE h2
  · have h2 := exp_half_le (n := n) (k := 2) (by omega)
    have ha := abs_bareRead_le hN (2 * n) β
    have hb := abs_bareRead_le hN n β
    have hab := abs_sub (bareRead hN (2 * n) β) (bareRead hN n β)
    calc _ ≤ (64 : ℝ) := by linarith
      _ ≤ 1024 / (2 : ℝ) ^ 2 := by norm_num
      _ ≤ 1024 / Real.exp (Real.log 2 / 2 * n) := div_le_div_of_nonneg_left (by norm_num) hE h2

/-! ## 4. The integrated form -/

/-- The strong-coupling bound on the doubling change at side `n`. DERIVED: `16 = 2⁴`; `4` the dimension;
`1024` and `log 2 / 2` from `finiteSize_decay_strong`. -/
def strongBound (n : ℕ) : ℝ := 16 * (n : ℝ) ^ 4 * (1024 * Real.exp (-(Real.log 2 / 2) * n))

/-- DERIVED: `65536 = 2^{16}`. -/
theorem abs_bareDelta_le (hN : N ≠ 0) {x : ℝ} (hx : |x| ≤ 1 / 65536) (n : ℕ) :
    |bareDelta hN n x| ≤ strongBound n := by
  unfold bareDelta strongBound
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 16 * (n : ℝ) ^ 4)]
  exact mul_le_mul_of_nonneg_left (finiteSize_decay_strong hN hx n) (by positivity)

/-- **The integrated strong part**: `|∫₀^β bareDelta hN n| ≤ β · 16 n⁴ · 1024 e^{−(log 2/2) n}` on
`0 ≤ β ≤ 2^{-16}`. DERIVED: `0` the lower coupling; `65536 = 2^{16}`. -/
theorem integral_bareDelta_strong_le (hN : N ≠ 0) (n : ℕ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 65536) :
    |∫ x in (0 : ℝ)..β, bareDelta hN n x| ≤ β * strongBound n := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := β)
    (f := fun x => bareDelta hN n x) (C := strongBound n) (fun x hx => by
      rw [Set.uIoc_of_le hβ0] at hx
      rw [Real.norm_eq_abs]
      exact abs_bareDelta_le hN (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩) n)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hβ0] at h
  linarith

/-- **The bare defect at strong coupling**: `|defectW N β n| ≤ β · 16 n⁴ · 1024 e^{−(log 2/2) n}` on
`0 ≤ β ≤ 2^{-16}`, `n ≠ 0`. DERIVED: `0` the excluded side and the lower coupling; `65536 = 2^{16}` the
strong-coupling threshold of `StrongKernelNear`. -/
theorem abs_defectW_strong_le (hN : N ≠ 0) {n : ℕ} (hn : n ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : β ≤ 1 / 65536) :
    |MassGap.ZoomSelfScale.defectW N β n| ≤ β * strongBound n := by
  rw [← MassGap.FlowComp.integral_bareDelta hN hn β]
  exact integral_bareDelta_strong_le hN n hβ0 hβ

/-- **`16 n⁴` is beaten by `e^{−(log 2/2) n}`**: `strongBound n → 0`. DERIVED: `4` the dimension; `2` the
base and the halving. -/
theorem tendsto_strongBound : Tendsto strongBound atTop (𝓝 0) := by
  have hc : 0 < Real.log 2 / 2 := by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  have hg := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
  have h := hg.const_mul (16 * 1024 * ((Real.log 2 / 2)⁻¹) ^ 4)
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, strongBound]
  rw [mul_pow, neg_mul]
  have hc' : (Real.log 2 / 2) ≠ 0 := hc.ne'
  field_simp

/-- For every `η > 0`, all large sides have `|defectW N β n| ≤ η` at every `β ∈ [0, 2^{-16}]`.
DERIVED: `65536 = 2^{16}`; `1` the least side. -/
theorem defectW_strong_eventually (hN : N ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ β : ℝ, 0 ≤ β → β ≤ 1 / 65536 → |MassGap.ZoomSelfScale.defectW N β n| ≤ η := by
  have hev := (tendsto_order.mp tendsto_strongBound).2 η hη
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1 β hβ0 hβ
  have hs : 0 ≤ strongBound n := by unfold strongBound; positivity
  calc _ ≤ β * strongBound n := abs_defectW_strong_le hN (by omega) hβ0 hβ
    _ ≤ 1 * strongBound n := mul_le_mul_of_nonneg_right (by linarith) hs
    _ ≤ η := by linarith

end MassGap.StrongFiniteSize

#print axioms MassGap.StrongFiniteSize.snorm_nbr
#print axioms MassGap.StrongFiniteSize.linkMod_injOn
#print axioms MassGap.StrongFiniteSize.plaqMod_injOn
#print axioms MassGap.StrongFiniteSize.torusState_sub_le
#print axioms MassGap.StrongFiniteSize.plaq_sub_le
#print axioms MassGap.StrongFiniteSize.bareRead_sub_le
#print axioms MassGap.StrongFiniteSize.finiteSize_decay_strong_pow
#print axioms MassGap.StrongFiniteSize.abs_bareRead_le
#print axioms MassGap.StrongFiniteSize.finiteSize_decay_strong
#print axioms MassGap.StrongFiniteSize.abs_bareDelta_le
#print axioms MassGap.StrongFiniteSize.integral_bareDelta_strong_le
#print axioms MassGap.StrongFiniteSize.abs_defectW_strong_le
#print axioms MassGap.StrongFiniteSize.tendsto_strongBound
#print axioms MassGap.StrongFiniteSize.defectW_strong_eventually
