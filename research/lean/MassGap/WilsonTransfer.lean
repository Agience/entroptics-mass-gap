import Mathlib
import MassGap.LogConvex

/-!
# MassGap.WilsonTransfer — the lattice time shift as an operator on Wilson observables

The time translation `Transfer.TransferData` asks for, built on the Wilson measure, together with
the two of its four fields that hold for it and the exact reason the other two cannot be stated on
the slab algebra.

## What the shift is, and why it costs nothing

`shiftConf τ U l = U (shiftLink τ l)` is one lattice step along `τ`, pulled back to configurations.
The one fact that carries everything is

    shiftConf τ U = reflConf τ c (reflConf τ (c + 1) U)          (`shiftConf_eq_reflConf_comp`)

for EVERY reflection constant `c`: a translation by one step is the composite of the two site
reflections whose constants differ by one. The dagger on the axis links appears twice and cancels, so
no new measure theory is needed — invariance of the Gibbs expectation under the shift
(`expect_shift_invariant`) is two applications of `Reflect.expect_reflect_invariant`, and the
conjugation identity a transfer operator needs,

    shiftConf τ (reflConf τ c (shiftConf τ U)) = reflConf τ c U  (`shiftConf_reflConf_shiftConf`)

is involutivity of the two reflections and nothing else.

## The four fields of `Transfer.TransferData`, one at a time

* `T` — `shiftObs τ` is an `ℝ`-linear endomorphism of the observables, and an algebra map
  (`shiftObs_one`, `shiftObs_mul`). On the FULL observable space, not on the slab algebra; see
  below.
* `T_symm` — `reflForm_shiftObs_symm`: `⟨T F, G⟩ = ⟨F, T G⟩` for the concrete Gibbs reflection form
  `Transfer.reflForm N τ c β`, at every real `β`, every reflection constant, and every pair of
  observables, with no measurability, boundedness or positivity hypothesis. This is what reflection
  positivity is for and it is the field that was expected to be hard; it is two lines once the
  composite identity is in hand.
* `T_vac` — `shiftObs_one`: the constant observable is translation-invariant, definitionally.
* `T_contract` — NOT proved here, and not provable on this module. Contractivity is Cauchy–Schwarz
  on a form that is positive semidefinite, iterated along the orbit `T^k x`; the form is positive
  semidefinite only on `LogConvex.localObs (blkS τ a m) (blkR τ a m)`
  (`ReflectionStrong.wilsonGibbsReflForm`), and that module is not stable under the shift.

## The obstruction, as a theorem rather than a remark

`shift_not_stable_on_slab` exhibits a link of `blkS ∪ blkR` — an axis link at level `m − 1` — whose
image under one step along `τ` is at level `m`, which `mem_blkS_union_blkR` refuses for an axis link.
So the shift moves the slab algebra off itself, and `shiftObs_mem` says where it goes: an observable
of `S ∪ R` becomes an observable of the image of `S ∪ R` under the shift. A transfer operator wants a
half-line; the site reflection's half-space on a periodic lattice is a slab of width `m` bounded
above by the second mirror plane. The two are not the same region and the shift is what tells them
apart.

The obstruction is not special to the direction chosen. The shift permutes the `n` levels cyclically,
so a set of links stable under it is stable under the whole cycle, and the only such subsets of the
levels are the empty one and all of them — while `blkS ∪ blkR` omits the axis levels `m` to `n − 1`.
The witness below is the concrete half of that statement.

Foundational footprint only (`#print axioms` at the end).
Build: `python research/code/lean_build.py build MassGap.WilsonTransfer`.
-/

namespace MassGap.WilsonTransfer

open MeasureTheory
open MassGap MassGap.Reflect MassGap.WilsonHypercubic MassGap.CompactGauge
open MassGap.ActionSplit MassGap.LogConvex

/-! ## Part 1 — the shift on sites and links -/

section Geometry

variable {d n : ℕ} [NeZero n]

/-- **One lattice step along `τ`, on links**: the direction is untouched and the base site moves by
`WilsonHypercubic.shift`.

DERIVED: no numeral of its own; the single step is `shift`'s, which is the definition of a
neighbouring site. -/
def shiftLink (τ : Fin d) (l : Link d n) : Link d n := (l.1, shift τ l.2)

@[simp] theorem shiftLink_fst (τ : Fin d) (l : Link d n) : (shiftLink τ l).1 = l.1 := rfl

@[simp] theorem shiftLink_snd (τ : Fin d) (l : Link d n) : (shiftLink τ l).2 = shift τ l.2 := rfl

/-- **Two reflections one apart compose to one step**, on sites: `(c+1) − (c − x) = x + 1`.

DERIVED: the `1`s are the gap between the two reflection constants and the one lattice step it
produces — the same `1`, read twice. -/
theorem reflSite_comp_succ (τ : Fin d) (c : Fin n) (x : Site d n) :
    reflSite τ (c + 1) (reflSite τ c x) = shift τ x := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp only [reflSite, shift, Function.update_self]
    abel
  · simp [reflSite, shift, Function.update_of_ne hj]

/-- The same statement with the lower constant written as a predecessor: `c − ((c−1) − x) = x + 1`.
This is the form the AXIS links need, since `reflLink` reflects them about `c − 1`. -/
theorem reflSite_comp_pred (τ : Fin d) (c : Fin n) (x : Site d n) :
    reflSite τ c (reflSite τ (c - 1) x) = shift τ x := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp only [reflSite, shift, Function.update_self]
    abel
  · simp [reflSite, shift, Function.update_of_ne hj]

@[simp] theorem reflLink_fst (τ : Fin d) (c : Fin n) (l : Link d n) :
    (reflLink τ c l).1 = l.1 := rfl

/-- **Two link reflections one apart compose to one step along the axis.** The axis links carry the
base shift `c − 1` on both reflections and come out at the same place as the transverse ones, which
is why a single statement covers the whole link set. -/
theorem reflLink_comp_succ (τ : Fin d) (c : Fin n) (l : Link d n) :
    reflLink τ (c + 1) (reflLink τ c l) = shiftLink τ l := by
  obtain ⟨μ, x⟩ := l
  by_cases h : μ = τ
  · have hc : c + 1 - 1 = c := by abel
    simp [reflLink, shiftLink, h, hc, reflSite_comp_pred]
  · simp [reflLink, shiftLink, h, reflSite_comp_succ]

end Geometry

/-! ## Part 2 — the shift on configurations, as a composite of two reflections -/

section Configs

variable {d n : ℕ} [NeZero n] {G : Type}

/-- **One lattice step along `τ`, on configurations.** A pure relabelling: unlike the reflection it
carries no dagger, because a translation does not reverse the traversal of an axis link. -/
def shiftConf (τ : Fin d) (U : Link d n → G) : Link d n → G := fun l => U (shiftLink τ l)

@[simp] theorem shiftConf_apply (τ : Fin d) (U : Link d n → G) (l : Link d n) :
    shiftConf τ U l = U (shiftLink τ l) := rfl

theorem measurable_shiftConf [MeasurableSpace G] (τ : Fin d) :
    Measurable (shiftConf (d := d) (n := n) (G := G) τ) :=
  measurable_pi_lambda _ (fun l => measurable_pi_apply (shiftLink τ l))

variable [Group G]

theorem reflConf_apply_axis (τ : Fin d) (c : Fin n) (U : Link d n → G) {l : Link d n}
    (h : l.1 = τ) : reflConf τ c U l = (U (reflLink τ c l))⁻¹ := by
  simp [reflConf, h]

theorem reflConf_apply_transverse (τ : Fin d) (c : Fin n) (U : Link d n → G) {l : Link d n}
    (h : l.1 ≠ τ) : reflConf τ c U l = U (reflLink τ c l) := by
  simp [reflConf, h]

/-- **THE ONE FACT THE WHOLE FILE RESTS ON: a step is two reflections one apart.**

`reflConf τ c ∘ reflConf τ (c+1)` is the translation by one step along `τ`, for EVERY `c`. On the
axis links each reflection inverts the gauge variable, so the two daggers cancel and the composite is
a bare relabelling; off the axis there is no dagger to cancel. The reflection constant does not
survive into the conclusion, which is what makes the composite a translation rather than a family of
them.

DERIVED: the `1` is the gap between the two reflection constants, and it is the same `1` as the
lattice step it produces (`reflSite_comp_succ`). -/
theorem shiftConf_eq_reflConf_comp (τ : Fin d) (c : Fin n) (U : Link d n → G) :
    shiftConf τ U = reflConf τ c (reflConf τ (c + 1) U) := by
  funext l
  have hfst : (reflLink τ c l).1 = l.1 := rfl
  by_cases h : l.1 = τ
  · rw [reflConf_apply_axis τ c _ h,
      reflConf_apply_axis τ (c + 1) U (hfst.trans h), inv_inv, reflLink_comp_succ]
    rfl
  · rw [reflConf_apply_transverse τ c _ h,
      reflConf_apply_transverse τ (c + 1) U (hfst.trans_ne h), reflLink_comp_succ]
    rfl

/-- **THE CONJUGATION IDENTITY A TRANSFER OPERATOR NEEDS**: the reflection turns a step into its
inverse, so stepping, reflecting and stepping again is reflecting.

This is `Θ ∘ S = S⁻¹ ∘ Θ` written without an inverse, and it is exactly what makes the time
translation self-adjoint for the reflection form. Its proof is the composite identity above plus
involutivity of the two reflections — no geometry beyond what `Reflect` already has. -/
theorem shiftConf_reflConf_shiftConf (τ : Fin d) (c : Fin n) (U : Link d n → G) :
    shiftConf τ (reflConf τ c (shiftConf τ U)) = reflConf τ c U := by
  have hinv : ∀ V : Link d n → G, reflConf τ c (reflConf τ c V) = V :=
    reflConf_involutive τ c
  have hinv' : ∀ V : Link d n → G, reflConf τ (c + 1) (reflConf τ (c + 1) V) = V :=
    reflConf_involutive τ (c + 1)
  rw [shiftConf_eq_reflConf_comp τ c (reflConf τ c (shiftConf τ U)),
    shiftConf_eq_reflConf_comp τ c U, hinv, hinv']

end Configs

/-! ## Part 3 — the Gibbs expectation is invariant under the shift -/

section Invariance

variable {d n : ℕ} [NeZero n]

/-- **THE GIBBS EXPECTATION OF THE WILSON SYSTEM IS INVARIANT UNDER ONE LATTICE STEP.**

The lattice's translation invariance, which the tree did not have: `LogConvex.EW_plaqE_pair_shift`
obtains a translated PAIR of plaquettes from a single reflection, and says in its own docstring that
no separate translation symmetry is needed for that; this is the symmetry itself, on an arbitrary
observable.

It needs no new measure theory. The shift is two reflections (`shiftConf_eq_reflConf_comp`) and the
Gibbs expectation is invariant under each (`Reflect.expect_reflect_invariant`), so the invariance is
that theorem twice.

DERIVED: the `0` is a reflection constant, and it is arbitrary — the identity holds at every `c`, and
`0` is picked only because a constant must be supplied. -/
theorem expect_shift_invariant (N : ℕ) (τ : Fin d) (β : ℝ)
    (O : (Link d n → MassGap.SUN.SU N) → ℝ) :
    (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β (fun U => O (shiftConf τ U))
      = (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β O := by
  have hstep : (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β
        (fun U => O (shiftConf τ U))
      = (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β
        (fun U => (fun V => O (reflConf τ (0 : Fin n) V)) (reflConf τ ((0 : Fin n) + 1) U)) :=
    MassGap.Transfer.expect_congr N β
      (fun U => by rw [shiftConf_eq_reflConf_comp τ (0 : Fin n) U])
  have h2 := MassGap.Reflect.expect_reflect_invariant N τ ((0 : Fin n) + 1) β
    (fun V => O (reflConf τ (0 : Fin n) V))
  have h1 := MassGap.Reflect.expect_reflect_invariant N τ (0 : Fin n) β O
  exact hstep.trans (h2.trans h1)

end Invariance

/-! ## Part 4 — the shift as a linear operator on observables

This is the `T` of `Transfer.TransferData`: an `ℝ`-linear endomorphism of the observables, in fact an
algebra map. It is carried on the FULL observable space because that is the largest space it IS an
endomorphism of; Part 6 shows it is not one on the slab algebra.
-/

section Operator

variable {d n N : ℕ} [NeZero n]

/-- **THE TIME TRANSLATION, AS A LINEAR OPERATOR ON OBSERVABLES**: `T F = F ∘ shiftConf`. -/
def shiftObs (τ : Fin d) :
    ((Link d n → MassGap.SUN.SU N) → ℝ) →ₗ[ℝ] ((Link d n → MassGap.SUN.SU N) → ℝ) where
  toFun F := fun U => F (shiftConf τ U)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem shiftObs_apply (τ : Fin d) (F : (Link d n → MassGap.SUN.SU N) → ℝ)
    (U : Link d n → MassGap.SUN.SU N) : shiftObs τ F U = F (shiftConf τ U) := rfl

/-- **`T 1 = 1` — `TransferData.T_vac`.** The shift of the constant observable is the constant
observable, definitionally.

DERIVED: the `1` is the constant observable's own value. -/
theorem shiftObs_one (τ : Fin d) :
    shiftObs (n := n) (N := N) τ (fun _ => (1 : ℝ)) = (fun _ => (1 : ℝ)) := rfl

/-- **The shift is an algebra map**, not merely linear — so it acts on the unital subalgebra
`ReflectionStrong.mul_mem_localObs` exhibits, wherever that algebra is stable under it. -/
theorem shiftObs_mul (τ : Fin d) (F G : (Link d n → MassGap.SUN.SU N) → ℝ) :
    shiftObs τ (fun U => F U * G U) = (fun U => shiftObs τ F U * shiftObs τ G U) := rfl

/-- **WHERE THE SHIFTED OBSERVABLE LIVES.** An observable reading `S ∪ R` becomes, after one step,
an observable reading the IMAGE of `S ∪ R` under the shift. Bounds and measurability carry across
unchanged; only the block moves.

This is the sharp form of the obstruction: paired with `shift_not_stable_on_slab`, which shows the
image is not contained in `blkS ∪ blkR`, it says the slab algebra is not stable under the shift and
names the algebra the shifted observable belongs to instead. -/
theorem shiftObs_mem (τ : Fin d) {S R E : Finset (Link d n)}
    {F : (Link d n → MassGap.SUN.SU N) → ℝ} (hF : F ∈ localObs S R)
    (hS : ∀ l ∈ S, shiftLink τ l ∈ E) (hR : ∀ l ∈ R, shiftLink τ l ∈ E) :
    shiftObs τ F ∈ localObs E (∅ : Finset (Link d n)) := by
  obtain ⟨hFm, ⟨C, hFb⟩, hFl⟩ := hF
  refine mem_localObs.mpr ⟨hFm.comp (measurable_shiftConf τ), ⟨C, fun U => hFb _⟩, ?_⟩
  intro U V hUE _
  exact hFl _ _ (fun i hi => hUE _ (hS i hi)) (fun i hi => hUE _ (hR i hi))

end Operator

/-! ## Part 5 — `T_symm`: the shift is self-adjoint for the Wilson reflection form -/

section Symm

variable {d n N : ℕ} [NeZero n]

/-- **`⟨T F, G⟩ = ⟨F, T G⟩` FOR THE WILSON GIBBS REFLECTION FORM** — `TransferData.T_symm`, on the
concrete form `Transfer.reflForm N τ c β` that `ReflectionStrong.wilsonGibbsReflForm` carries.

No hypothesis at all: every real `β`, every reflection constant, every pair of observables, no
measurability, no boundedness, no positivity. The two ingredients are invariance of the Gibbs
expectation under the shift (`expect_shift_invariant`) and the conjugation identity
(`shiftConf_reflConf_shiftConf`) — which is what "reflection positivity is what makes the time
translation self-adjoint" means concretely.

DERIVED: no numeral. -/
theorem reflForm_shiftObs_symm (N : ℕ) (τ : Fin d) (c : Fin n) (β : ℝ)
    (F G : (Link d n → MassGap.SUN.SU N) → ℝ) :
    MassGap.Transfer.reflForm N τ c β (shiftObs τ F) G
      = MassGap.Transfer.reflForm N τ c β F (shiftObs τ G) := by
  have hcancel : ∀ U : Link d n → MassGap.SUN.SU N,
      F (shiftConf τ (reflConf τ c (shiftConf τ U))) * G (shiftConf τ U)
        = F (reflConf τ c U) * G (shiftConf τ U) := by
    intro U
    rw [shiftConf_reflConf_shiftConf τ c U]
  have h := expect_shift_invariant N τ β (fun U => F (shiftConf τ (reflConf τ c U)) * G U)
  exact h.symm.trans (MassGap.Transfer.expect_congr N β hcancel)

end Symm

/-! ## Part 6 — the slab is not stable under the shift

The structural blocker, as a witness rather than a remark.
-/

section Blocker

variable {d n : ℕ} [NeZero n]

/-- **AN AXIS LINK AT LEVEL `m − 1` IS IN THE SLAB AND ITS IMAGE IS NOT.**

`mem_blkS_union_blkR` admits an axis link exactly when its level is strictly below `m`; one step
along `τ` takes level `m − 1` to level `m` (`lv_shift_axis`), which is refused. So the one-step shift
is not an endomorphism of the slab algebra, and `TransferData.T` cannot be instantiated by it there.

DERIVED: `m − 1` is the highest axis level the slab admits and `m` is the first it refuses; both are
read off `mem_blkS_union_blkR`, not chosen. -/
theorem shiftLink_axis_leaves_slab (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m) (hm0 : 0 < m)
    {l : Link d n} (hl1 : l.1 = τ) (hlv : lv a (l.2 τ) = m - 1) :
    l ∈ blkS τ a m ∪ blkR τ a m ∧ shiftLink τ l ∉ blkS τ a m ∪ blkR τ a m := by
  have hmn : m < n := by omega
  constructor
  · rw [mem_blkS_union_blkR, if_pos hl1, hlv]
    omega
  · rw [mem_blkS_union_blkR, if_pos (show (shiftLink τ l).1 = τ from hl1), shiftLink_snd,
      lv_shift_axis, hlv]
    have hs : m - 1 + 1 = m := by omega
    rw [hs, Nat.mod_eq_of_lt hmn]
    omega

/-- **THE SLAB ALGEBRA IS NOT STABLE UNDER ONE LATTICE STEP** — the blocker, existentially.

A `Transfer.TransferData` on `LogConvex.localObs (blkS τ a m) (blkR τ a m)` needs `T` to be an
endomorphism of that module. By `shiftObs_mem` the shifted observable reads the image of the block
under `shiftLink`, and this says that image is not inside the block. The site reflection's half-space
on a periodic lattice is a SLAB bounded above by the second mirror plane; a transfer operator wants a
half-line.

DERIVED: no numeral of its own; the witness is `shiftLink_axis_leaves_slab`'s. -/
theorem shift_not_stable_on_slab (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m) (hm0 : 0 < m) :
    ∃ l ∈ blkS τ a m ∪ blkR τ a m, shiftLink τ l ∉ blkS τ a m ∪ blkR τ a m := by
  have hlt : m - 1 < n := by omega
  refine ⟨(τ, fun _ => a + fcast n (m - 1)), ?_, ?_⟩
  · exact (shiftLink_axis_leaves_slab τ a m hm hm0 (l := (τ, fun _ => a + fcast n (m - 1)))
      rfl (lv_add_fcast a (m - 1) hlt)).1
  · exact (shiftLink_axis_leaves_slab τ a m hm hm0 (l := (τ, fun _ => a + fcast n (m - 1)))
      rfl (lv_add_fcast a (m - 1) hlt)).2

end Blocker

#print axioms shiftLink
#print axioms reflSite_comp_succ
#print axioms reflSite_comp_pred
#print axioms reflLink_comp_succ
#print axioms shiftConf
#print axioms measurable_shiftConf
#print axioms reflConf_apply_axis
#print axioms reflConf_apply_transverse
#print axioms shiftConf_eq_reflConf_comp
#print axioms shiftConf_reflConf_shiftConf
#print axioms expect_shift_invariant
#print axioms shiftObs
#print axioms shiftObs_one
#print axioms shiftObs_mul
#print axioms shiftObs_mem
#print axioms reflForm_shiftObs_symm
#print axioms shiftLink_axis_leaves_slab
#print axioms shift_not_stable_on_slab

end MassGap.WilsonTransfer
