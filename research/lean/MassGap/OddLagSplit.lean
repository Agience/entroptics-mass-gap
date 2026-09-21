import Mathlib
import MassGap.CrossingIntegration
import MassGap.PlaqVariance
import MassGap.HaarMoments

/-!
# MassGap.OddLagSplit — the odd-lag (link-reflection) action split

`ActionSplit` splits the Wilson action at a SITE-reflection plane (even extent, even lag) and proves
the Osterwalder–Seiler pairing inequality there. `CrossingIntegration` supplies the analytic engine
for the remaining case and states its own two limits. This file is the LINK-reflection geometry: even
extent `n = 2m`, ODD lag `c`, where `2x = c` has no solution and `2x = c − 1` has two.

## Part A — the obstruction, at the level of the SUM

`CrossingIntegration`'s two obstructions are stated for ONE straddling plaquette, and its scope note
records that the Boltzmann weight's straddling factor is the exponential of a SUM, so neither
theorem rules out that the SUM is a paired form. It names a witness that should lift and does not
build it. It is built here and it does lift.

`cfgSum` carries `gNeg = diag(1, −1, −1)` on every reflection-FIXED axis link whose site coordinates
have EVEN SUM, and the identity everywhere else. Two facts make it work:

* it is reflection-fixed (`reflConf_cfgSum`) — every link carries `1` or `gNeg`, both self-inverse,
  and the reflection inverts only the axis links, mapping fixed ones to themselves and non-fixed ones
  to other non-fixed ones; and
* a transverse step FLIPS the coordinate-sum parity when the extent is even
  (`sum_val_shift_parity`), so of the two fixed axis links a straddling plaquette reads, EXACTLY ONE
  carries `gNeg` — and the word is `gNeg` at every straddling plaquette at once
  (`hol_cfgSum_oddCross`).

So the straddling sum reads `−card` where a paired form would read `≥ 0`
(`straddling_sum_not_paired_at_odd_lag`), and it reads `−card` against `3 · card` at the identity
while both half-restrictions are untouched (`no_half_function_for_straddling_sum`). Both obstructions
lift; the second lifts with no parity argument at all, since the fixed axis links are absent from
both halves however many plaquettes read them.

## Part B — the block partition at a link-reflection plane

`oblkR` is the fixed set: the AXIS links at levels `0` and `m` measured from `a`, where `a + a = c − 1`
(two planes, because the extent is periodic). `oblkS` and `oblkT` are the two open sides. The
reflection carries `oblkS` onto `oblkT` (`oblkS_maps_oblkT`) and fixes `oblkR` pointwise
(`oblkR_fixed`), which `reflConf` then INVERTS — that inversion is the whole difference from the
even-lag case.

`oplaq_side` is the trichotomy: a non-degenerate plaquette reads `oblkS` alone, reads `oblkT` alone,
or STRADDLES, and the straddling ones are exactly those with one direction along the axis and a base
site at level `0` or `m` (`oplqCross`). Unlike the even-lag case the one-sided plaquettes touch the
fixed set not at all: `R` appears only in the straddling words.

## Part C — the direct sum, which is what a SUM of straddling plaquettes needs

`CrossingIntegration.hsRe_conj` is one matrix pair under one gauge pair; `wilson_crossing_pairing_nonneg`
reads a single `X`. A sum of straddling words is a block-diagonal `X`: `dsum` builds it,
`hsRe_dsum` says the cross form of two block-diagonal matrices is the sum of the blocks' cross forms,
and `hsRe_dsum_conj` is `hsRe_conj` for a whole family at once, each block conjugated by its own
gauge pair. That is the direct-sum form the aggregation needs.

## Part D — the straddling word IS the gauge-transformed cross form

`cross_word_level_zero` and `cross_word_level_m` compute the straddling plaquette's holonomy at each
of the two fixed planes and exhibit it as `g · F · g'⁻¹ · F̄⁻¹`, the Wilson cross form of one
transverse link against another with the plane links absorbed as a gauge. `hsRe_cross_word` is that
statement in `hsRe` form, which is what `CrossingIntegration` consumes.

## Parts E to K — the discharge

Parts E to G do the measure theory: `integral_three_block` factors the product Haar over
`oblkR ⊔ oblkS ⊔ oblkT` as an iterated integral with the integrand still coupling all three,
`integral_oblk_mirror` transports the mirror's variables onto the positive half so both inner
integrals run over the same block, and `plane_group_haar`, `planeAct_measurePreserving`,
`measurable_uncurry_planeAct` and `abs_coord_le_one_of_entries` supply every instance the crossing
integration asks for. Part H chooses the plane: every odd lag is `a + a + 1` for some `a`, and one of
the two choices puts the base plaquette inside the positive half
(`exists_odd_lag_plane_in_half`).

Parts I to K identify the integrand. `oplqCross` indexes the blocks directly — both orientations of
every geometric plaquette, both fixed planes — and after inverting the gauge on the upper plane alone
every block reads `hsRe (g̃(A) · U(S) · g̃(B)⁻¹) (U(T))` (`re_tr_hol_cross`). `crossWord` is the
direct sum of those, `planeA`/`planeB` run the assignment backwards from a half-link to its
plaquette's plane links, and `sum_re_tr_oplqCross` is the whole straddling factor as ONE cross form.

`corrClay_reflection_positive` is the conclusion: the body of
`Complete.wilson_reflection_positive_at` at aperture `Nap`, with no hypothesis about the lattice
left. It carries `2 ≤ m` — extent at least four, because the backward plane assignment collides at
extent two (`negctl_plane_assignment_collides_at_m_one`) — and `0 ≤ β`, because the Wilson cross
kernel is positive-semidefinite exactly there
(`negctl_odd_discharge_needs_nonneg_coupling`).

Foundational footprint only (`#print axioms` at the end).
Build: `python code/lean_build.py build MassGap.OddLagSplit`.
-/

namespace MassGap.OddLagSplit

open MeasureTheory
open MassGap MassGap.ActionSplit MassGap.CharacterExpansion MassGap.CrossingIntegration
open MassGap.WilsonLattice MassGap.WilsonHypercubic
open MassGap.CompactGauge MassGap.Reflect

/-! ## Part A — the obstruction lifted to the SUM

### The parity that separates the two fixed axis links of a straddling plaquette -/

section Parity

variable {d n : ℕ} [NeZero n]

/-- The coordinate sum of a site, as a natural number. Its PARITY is the only thing used. -/
def siteSum (x : Site d n) : ℕ := ∑ k, (x k).val

/-- **A transverse step flips the coordinate-sum parity, at even extent.**

Stepping in direction `ν` replaces `x ν` by `x ν + 1` and leaves every other coordinate alone, so the
two sums differ by the one coordinate. When the step does not wrap, the change is `+1`; when it wraps,
the coordinate drops from `n − 1` to `0`, and `n − 1` is ODD because the extent is even. So the
parity flips either way — which is what makes the two fixed axis links of a straddling plaquette
carry DIFFERENT group elements.

DERIVED: `1` is one lattice step; the evenness of `n` is the hypothesis, not a choice. -/
theorem sum_val_shift_parity (hn : Even n) (ν : Fin d) (x : Site d n) :
    ¬ (Even (siteSum (shift ν x)) ↔ Even (siteSum x)) := by
  classical
  have hagree : ∀ k ∈ Finset.univ.erase ν, ((shift ν x) k).val = (x k).val := by
    intro k hk
    have hkν : k ≠ ν := Finset.ne_of_mem_erase hk
    simp [shift, Function.update_of_ne hkν]
  have hshiftν : ((shift ν x) ν).val = ((x ν).val + 1) % n := by
    have h1 : (shift ν x) ν = x ν + 1 := by simp [shift]
    rw [h1, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  have hA : siteSum (shift ν x)
      = ((x ν).val + 1) % n + ∑ k ∈ Finset.univ.erase ν, (x k).val := by
    rw [siteSum, ← Finset.add_sum_erase _ _ (Finset.mem_univ ν), hshiftν,
      Finset.sum_congr rfl hagree]
  have hB : siteSum x = (x ν).val + ∑ k ∈ Finset.univ.erase ν, (x k).val := by
    rw [siteSum, ← Finset.add_sum_erase _ _ (Finset.mem_univ ν)]
  -- the one coordinate's contribution is odd
  have hodd : Odd (((x ν).val + 1) % n + (x ν).val) := by
    obtain ⟨r, hr⟩ := hn
    have hv : (x ν).val < n := (x ν).isLt
    rcases Nat.lt_or_ge ((x ν).val + 1) n with h | h
    · rw [Nat.mod_eq_of_lt h]
      exact ⟨(x ν).val, by omega⟩
    · have he : (x ν).val + 1 = n := by omega
      rw [he, Nat.mod_self]
      exact ⟨r - 1, by omega⟩
  have hsum : siteSum (shift ν x) + siteSum x
      = (((x ν).val + 1) % n + (x ν).val)
        + ((∑ k ∈ Finset.univ.erase ν, (x k).val) + ∑ k ∈ Finset.univ.erase ν, (x k).val) := by
    rw [hA, hB]; ring
  intro hiff
  have h1 : Even (siteSum (shift ν x) + siteSum x) := Nat.even_add.mpr hiff
  rw [hsum] at h1
  have h2 : Even ((∑ k ∈ Finset.univ.erase ν, (x k).val)
      + ∑ k ∈ Finset.univ.erase ν, (x k).val) := ⟨_, rfl⟩
  exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_add.mp h1).mpr h2)

end Parity

/-! ### The witness: `gNeg` on every fixed axis link of even coordinate sum -/

section SumWitness

variable {d n : ℕ} [NeZero n]

open Classical in
/-- **THE SUM-LEVEL WITNESS.** `gNeg = diag(1, −1, −1)` on every reflection-FIXED axis link whose
site coordinates have even sum; the identity on every other link.

This is the configuration `CrossingIntegration`'s scope note names and does not build. Its point is
that a straddling plaquette reads TWO fixed axis links whose sites differ by one transverse step, so
by `sum_val_shift_parity` exactly ONE of them carries `gNeg` — and the plaquette word is `gNeg` no
matter which.

DERIVED: `3` is the rank of the gauge group the development is built at, and the size `gNeg` already
has; `1` is the identity element, which is what every link the witness does not touch carries. -/
noncomputable def cfgSum (τ : Fin d) (c : Fin n) : Link d n → MassGap.SUN.SU 3 :=
  fun l => if l.1 = τ ∧ reflLink τ c l = l ∧ Even (siteSum l.2) then gNeg else 1

variable {τ : Fin d} {c : Fin n}

theorem cfgSum_gNeg {l : Link d n} (h1 : l.1 = τ) (h2 : reflLink τ c l = l)
    (h3 : Even (siteSum l.2)) : cfgSum τ c l = gNeg := by
  classical
  simp only [cfgSum]
  rw [if_pos ⟨h1, h2, h3⟩]

theorem cfgSum_one_of_dir {l : Link d n} (h : l.1 ≠ τ) : cfgSum τ c l = 1 := by
  classical
  simp only [cfgSum]
  rw [if_neg (fun hc => h hc.1)]

theorem cfgSum_one_of_not_fixed {l : Link d n} (h : reflLink τ c l ≠ l) : cfgSum τ c l = 1 := by
  classical
  simp only [cfgSum]
  rw [if_neg (fun hc => h hc.2.1)]

theorem cfgSum_one_of_odd {l : Link d n} (h : ¬ Even (siteSum l.2)) : cfgSum τ c l = 1 := by
  classical
  simp only [cfgSum]
  rw [if_neg (fun hc => h hc.2.2)]

/-- **Every value of the witness is its own inverse** — `1` and `gNeg` both are. This is what makes
the configuration reflection-fixed even though the reflection DAGGERS the axis links. -/
theorem cfgSum_inv (l : Link d n) : (cfgSum τ c l)⁻¹ = cfgSum τ c l := by
  classical
  simp only [cfgSum]
  split
  · exact gNeg_inv
  · exact inv_one

/-- **THE WITNESS IS REFLECTION-FIXED.**

On a fixed axis link the reflection inverts and the value is self-inverse. On a non-fixed axis link
the reflection reads the partner link, which is also non-fixed (the reflection is an involution), so
both carry the identity. On a transverse link the reflection reads another transverse link, and the
witness is the identity on all of them. -/
theorem reflConf_cfgSum (τ : Fin d) (c : Fin n) :
    reflConf τ c (cfgSum τ c) = cfgSum τ c := by
  funext l
  show (if l.1 = τ then (cfgSum τ c (reflLink τ c l))⁻¹ else cfgSum τ c (reflLink τ c l))
      = cfgSum τ c l
  by_cases hdir : l.1 = τ
  · rw [if_pos hdir]
    by_cases hfix : reflLink τ c l = l
    · rw [hfix, cfgSum_inv]
    · have hfix2 : reflLink τ c (reflLink τ c l) ≠ reflLink τ c l := by
        rw [reflLink_involutive τ c l]
        exact fun hc => hfix hc.symm
      rw [cfgSum_one_of_not_fixed hfix2, cfgSum_one_of_not_fixed hfix, inv_one]
  · rw [if_neg hdir]
    have hdir2 : (reflLink τ c l).1 ≠ τ := hdir
    rw [cfgSum_one_of_dir hdir2, cfgSum_one_of_dir hdir]

end SumWitness

/-! ### The straddling plaquettes of a link reflection, and the witness's word on all of them -/

section OddCross

variable {d n : ℕ} [NeZero n]

/-- **A straddling plaquette of a link reflection**: one direction along the axis and one across it,
with a base site whose AXIS link the reflection fixes.

`CharacterExpansion.odd_lag_straddling_plaq_two_fixed_axis_links` produces exactly such a plaquette
at even extent and odd lag, and `oplaq_side` below proves these are ALL of the straddling ones. -/
def OddCross (τ : Fin d) (c : Fin n) (q : Plaq d n) : Prop :=
  q.1.1 ≠ q.1.2 ∧ (q.1.1 = τ ∨ q.1.2 = τ) ∧ reflLink τ c ((τ, q.2) : Link d n) = (τ, q.2)

/-- The SECOND fixed axis link a straddling plaquette reads: the transverse step does not move the
axis coordinate, so its midpoint is the same plane. -/
theorem reflLink_fixed_shift {τ ν : Fin d} (hν : ν ≠ τ) (c : Fin n) {x : Site d n}
    (h : reflLink τ c ((τ, x) : Link d n) = (τ, x)) :
    reflLink τ c ((τ, shift ν x) : Link d n) = (τ, shift ν x) := by
  refine (reflLink_fixed_iff_axis c _ rfl).mpr ?_
  have hx := (reflLink_fixed_iff_axis c ((τ, x) : Link d n) rfl).mp h
  have hs : (shift ν x) τ = x τ := by
    simp [shift, Function.update_of_ne (Ne.symm hν)]
  show c - 1 = (shift ν x) τ + (shift ν x) τ
  rw [hs]
  exact hx

/-- **THE WITNESS'S WORD IS `gNeg` AT EVERY STRADDLING PLAQUETTE AT ONCE.**

The two transverse links carry the identity because their direction is not the axis. The two axis
links are both reflection-fixed and their sites differ by one transverse step, so by
`sum_val_shift_parity` exactly one of them carries `gNeg`. Whichever it is, the word reduces to
`gNeg` or to `gNeg⁻¹`, which is the same element.

This is the step `CrossingIntegration`'s `cfgWitness` could not take: that configuration made ONE
plaquette read `−1` and left every other straddling plaquette at `+3`. -/
theorem cfgSum_pair (hn : Even n) {τ ρ : Fin d} (hρ : ρ ≠ τ) {c : Fin n} {x : Site d n}
    (hfix : reflLink τ c ((τ, x) : Link d n) = (τ, x)) :
    (cfgSum τ c ((τ, x) : Link d n) = gNeg
        ∧ cfgSum τ c ((τ, shift ρ x) : Link d n) = 1)
      ∨ (cfgSum τ c ((τ, x) : Link d n) = 1
        ∧ cfgSum τ c ((τ, shift ρ x) : Link d n) = gNeg) := by
  have hfix2 : reflLink τ c ((τ, shift ρ x) : Link d n) = (τ, shift ρ x) :=
    reflLink_fixed_shift hρ c hfix
  have hpar := sum_val_shift_parity hn ρ x
  by_cases hx : Even (siteSum x)
  · have hodd : ¬ Even (siteSum (shift ρ x)) := fun hc => hpar ⟨fun _ => hx, fun _ => hc⟩
    exact Or.inl ⟨cfgSum_gNeg (l := ((τ, x) : Link d n)) rfl hfix hx,
      cfgSum_one_of_odd (l := ((τ, shift ρ x) : Link d n)) hodd⟩
  · have hev : Even (siteSum (shift ρ x)) := by
      by_contra hc
      exact hpar ⟨fun h => absurd h hc, fun h => absurd h hx⟩
    exact Or.inr ⟨cfgSum_one_of_odd (l := ((τ, x) : Link d n)) hx,
      cfgSum_gNeg (l := ((τ, shift ρ x) : Link d n)) rfl hfix2 hev⟩

/-- The straddling word at `((τ, ν), x)`: the two transverse links drop out and the two fixed axis
links leave exactly one `gNeg`. -/
theorem hol_cfgSum_left (hn : Even n) {τ ν : Fin d} (hν : ν ≠ τ) {c : Fin n} {x : Site d n}
    (hfix : reflLink τ c ((τ, x) : Link d n) = (τ, x)) :
    wilsonHol (bd (d := d) (n := n)) (((τ, ν), x) : Plaq d n) (cfgSum τ c) = gNeg := by
  have h2 : cfgSum τ c ((ν, shift τ x) : Link d n) = 1 := cfgSum_one_of_dir hν
  have h4 : cfgSum τ c ((ν, x) : Link d n) = 1 := cfgSum_one_of_dir hν
  rcases cfgSum_pair hn hν hfix with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp [wilsonHol, bd, ha, hb, h2, h4]
  · simp [wilsonHol, bd, ha, hb, h2, h4, gNeg_inv]

/-- The straddling word at the reversed orientation `((ν, τ), x)`, which is the same element. -/
theorem hol_cfgSum_right (hn : Even n) {τ ν : Fin d} (hν : ν ≠ τ) {c : Fin n} {x : Site d n}
    (hfix : reflLink τ c ((τ, x) : Link d n) = (τ, x)) :
    wilsonHol (bd (d := d) (n := n)) (((ν, τ), x) : Plaq d n) (cfgSum τ c) = gNeg := by
  have h1 : cfgSum τ c ((ν, x) : Link d n) = 1 := cfgSum_one_of_dir hν
  have h3 : cfgSum τ c ((ν, shift τ x) : Link d n) = 1 := cfgSum_one_of_dir hν
  rcases cfgSum_pair hn hν hfix with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp [wilsonHol, bd, ha, hb, h1, h3, gNeg_inv]
  · simp [wilsonHol, bd, ha, hb, h1, h3]

theorem hol_cfgSum_oddCross (hn : Even n) {τ : Fin d} {c : Fin n} {q : Plaq d n}
    (hq : OddCross τ c q) :
    wilsonHol (bd (d := d) (n := n)) q (cfgSum τ c) = gNeg := by
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  obtain ⟨hne, hax, hfix⟩ := hq
  have hne' : μ ≠ ν := hne
  have hfix' : reflLink τ c ((τ, x) : Link d n) = (τ, x) := hfix
  rcases hax with hμ | hν
  · have hμ' : μ = τ := hμ
    have hq : (((μ, ν), x) : Plaq d n) = ((τ, ν), x) := by rw [hμ']
    have hρ : ν ≠ τ := fun hc => hne' (hμ'.trans hc.symm)
    rw [hq]
    exact hol_cfgSum_left hn hρ hfix'
  · have hν' : ν = τ := hν
    have hq : (((μ, ν), x) : Plaq d n) = ((μ, τ), x) := by rw [hν']
    have hρ : μ ≠ τ := fun hc => hne' (hc.trans hν'.symm)
    rw [hq]
    exact hol_cfgSum_right hn hρ hfix'

/-- **The straddling SUM at the witness is `−card`.** Every term is `Re tr gNeg = −1`. -/
theorem sum_re_tr_cfgSum (hn : Even n) {τ : Fin d} {c : Fin n} (A : Finset (Plaq d n))
    (hA : ∀ q ∈ A, OddCross τ c q) :
    (∑ q ∈ A, (Matrix.trace
        ((wilsonHol (bd (d := d) (n := n)) q (cfgSum τ c) : MassGap.SUN.SU 3)
          : Matrix (Fin 3) (Fin 3) ℂ)).re) = -(A.card : ℝ) := by
  have hterm : ∀ q ∈ A, (Matrix.trace
      ((wilsonHol (bd (d := d) (n := n)) q (cfgSum τ c) : MassGap.SUN.SU 3)
        : Matrix (Fin 3) (Fin 3) ℂ)).re = -1 := by
    intro q hq
    rw [hol_cfgSum_oddCross hn (hA q hq), trace_gNeg]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **The straddling SUM at the identity is `3 · card`.** The control value the witness is measured
against — the same sum with the plane links set to the identity.

DERIVED: `3` is `Re tr 1` in `SU(3)`, the rank. -/
theorem sum_re_tr_one (A : Finset (Plaq d n)) :
    (∑ _q ∈ A, (Matrix.trace
        ((wilsonHol (bd (d := d) (n := n)) _q (fun _ => (1 : MassGap.SUN.SU 3))
          : MassGap.SUN.SU 3) : Matrix (Fin 3) (Fin 3) ℂ)).re) = 3 * (A.card : ℝ) := by
  have hterm : ∀ q ∈ A, (Matrix.trace
      ((wilsonHol (bd (d := d) (n := n)) q (fun _ => (1 : MassGap.SUN.SU 3))
        : MassGap.SUN.SU 3) : Matrix (Fin 3) (Fin 3) ℂ)).re = 3 := by
    intro q _
    have hone : wilsonHol (bd (d := d) (n := n)) q (fun _ => (1 : MassGap.SUN.SU 3)) = 1 := by
      simp [wilsonHol, bd]
    rw [hone, Submonoid.coe_one, Matrix.trace_one]
    norm_num
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  ring

end OddCross

/-! ### THE ANSWER TO THE SCOPED QUESTION: the obstruction LIFTS to the sum -/

section SumAnswer

variable {d n : ℕ} [NeZero n]

/-- **THE SCOPED CLAIM, SETTLED — the SUM is not a paired form either.**

`CrossingIntegration.straddling_word_not_paired_at_odd_lag` is about ONE straddling plaquette and its
scope note says so. This is the same statement for the whole straddling factor: for ANY nonempty
finite family of straddling plaquettes, the sum of their words' `Re tr` is not a nonnegative
combination of paired forms `hsRe (X ·) (X (Θ ·))`, for any finite family `X` reading anything.

The witness `cfgSum` is reflection-fixed and makes EVERY straddling plaquette read `−1` at once, so
the sum reads `−card < 0` where a paired form would be a sum of squares.

DERIVED: `−1` is the computed `Re tr` of `diag(1, −1, −1)`; `card` is the number of plaquettes in the
family; `0` is the sign a square has. -/
theorem straddling_sum_not_paired_at_odd_lag (hn : Even n) {τ : Fin d} {c : Fin n}
    (A : Finset (Plaq d n)) (hA : ∀ q ∈ A, OddCross τ c q) (hAne : A.Nonempty)
    {K : Type} [Fintype K] {Nc : ℕ} (cf : K → ℝ) (hcf : ∀ k, 0 ≤ cf k)
    (X : K → (Link d n → MassGap.SUN.SU 3) → Matrix (Fin Nc) (Fin Nc) ℂ) :
    ¬ ∀ U : Link d n → MassGap.SUN.SU 3,
      (∑ q ∈ A, (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) q U : MassGap.SUN.SU 3)
          : Matrix (Fin 3) (Fin 3) ℂ)).re)
        = ∑ k, cf k * hsRe (X k U) (X k (reflConf τ c U)) := by
  intro h
  have hpos : 0 ≤ ∑ k, cf k * hsRe (X k (cfgSum τ c)) (X k (reflConf τ c (cfgSum τ c))) :=
    paired_sum_nonneg_at_fixed (reflConf τ c) (reflConf_cfgSum τ c) cf hcf X
  rw [← h (cfgSum τ c), sum_re_tr_cfgSum hn A hA] at hpos
  have hcard : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hAne
  linarith

/-- **The same for the literal matrix form.** The straddling factor's word is not `X · (ΘX)ᴴ`. -/
theorem straddling_sum_not_matrix_paired_at_odd_lag (hn : Even n) {τ : Fin d} {c : Fin n}
    (A : Finset (Plaq d n)) (hA : ∀ q ∈ A, OddCross τ c q) (hAne : A.Nonempty)
    {Nc : ℕ} (X : (Link d n → MassGap.SUN.SU 3) → Matrix (Fin Nc) (Fin Nc) ℂ) :
    ¬ ∀ U : Link d n → MassGap.SUN.SU 3,
      (∑ q ∈ A, (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) q U : MassGap.SUN.SU 3)
          : Matrix (Fin 3) (Fin 3) ℂ)).re)
        = hsRe (X U) (X (reflConf τ c U)) := by
  intro h
  have hpos : 0 ≤ hsRe (X (cfgSum τ c)) (X (reflConf τ c (cfgSum τ c))) := by
    rw [reflConf_cfgSum τ c]
    exact hsRe_self_nonneg _
  rw [← h (cfgSum τ c), sum_re_tr_cfgSum hn A hA] at hpos
  have hcard : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hAne
  linarith

/-- **THE SECOND OBSTRUCTION LIFTS, and it lifts with no parity argument at all.**

A reflection-fixed axis link lies in NEITHER half — it cannot, since the reflection fixes it while
`S` and `T` are disjoint and the reflection carries `S` into `T`. That is true however many
plaquettes read it, so the straddling SUM is no more a function of the two half-restrictions than one
straddling word is. The two configurations are the identity and `cfgSum`, which agree on `S` and
whose reflections agree on `S`, and whose straddling sums are `3 · card` and `−card`.

DERIVED: `3` and `−1` are computed traces; `card` is the family's size. -/
theorem no_half_function_for_straddling_sum (hn : Even n) {τ : Fin d} {c : Fin n}
    (A : Finset (Plaq d n)) (hA : ∀ q ∈ A, OddCross τ c q) (hAne : A.Nonempty)
    (S T : Finset (Link d n)) (hST : Disjoint S T)
    (hSmap : ∀ l ∈ S, reflLink τ c l ∈ T)
    (Φ : (S → MassGap.SUN.SU 3) → (S → MassGap.SUN.SU 3) → ℝ) :
    ¬ ∀ U : Link d n → MassGap.SUN.SU 3,
      (∑ q ∈ A, (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) q U : MassGap.SUN.SU 3)
          : Matrix (Fin 3) (Fin 3) ℂ)).re)
        = Φ (fun l : S => U (l : Link d n)) (fun l : S => reflConf τ c U (l : Link d n)) := by
  intro h
  -- no link of `S` is reflection-fixed
  have hSnotfix : ∀ l ∈ S, reflLink τ c l ≠ l := by
    intro l hl hcon
    exact (Finset.disjoint_left.mp hST) hl (hcon ▸ hSmap l hl)
  -- so the witness is the identity on `S`
  have hSone : ∀ l ∈ S, cfgSum τ c l = 1 := fun l hl => cfgSum_one_of_not_fixed (hSnotfix l hl)
  have hone := h (fun _ => (1 : MassGap.SUN.SU 3))
  have hwit := h (cfgSum τ c)
  rw [sum_re_tr_one A] at hone
  rw [sum_re_tr_cfgSum hn A hA] at hwit
  have hΘone : reflConf τ c (fun _ : Link d n => (1 : MassGap.SUN.SU 3)) = (fun _ => 1) := by
    funext l
    show (if l.1 = τ then (1 : MassGap.SUN.SU 3)⁻¹ else 1) = 1
    simp
  have harg1 : (fun l : S => cfgSum τ c (l : Link d n))
      = (fun l : S => (1 : MassGap.SUN.SU 3)) := by
    funext l; exact hSone (l : Link d n) l.2
  have harg2 : (fun l : S => reflConf τ c (cfgSum τ c) (l : Link d n))
      = (fun l : S => reflConf τ c (fun _ : Link d n => (1 : MassGap.SUN.SU 3)) (l : Link d n)) := by
    rw [reflConf_cfgSum τ c, hΘone]
    funext l; exact hSone (l : Link d n) l.2
  rw [harg1, harg2] at hwit
  rw [hΘone] at hone hwit
  have hcard : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hAne
  have hbad : -(A.card : ℝ) = 3 * (A.card : ℝ) := hwit.trans hone.symm
  linarith

end SumAnswer

/-! ### Non-vacuity and negative controls for Part A -/

section SumControls

variable {d n : ℕ} [NeZero n]

/-- **The straddling set is nonempty at even extent and odd lag** — the family the theorems above
quantify over actually exists. Built from the fixed axis link
`ActionSplit.odd_lag_has_fixed_axis_link` supplies. -/
theorem exists_oddCross (hn : Even n) (h2 : 2 ≤ n) {τ ν : Fin d} (hν : ν ≠ τ)
    {c : Fin n} (hc : ¬ Even c.val) : ∃ q : Plaq d n, OddCross τ c q := by
  obtain ⟨y, hy⟩ := exists_fixed_site (even_sub_one_of_odd hn h2 hc)
  refine ⟨((τ, ν), Function.update (fun _ => 0) τ y), fun hcon => hν hcon.symm, Or.inl rfl, ?_⟩
  refine (reflLink_fixed_iff_axis c _ rfl).mpr ?_
  simpa using hy.symm

/-- **THE REFUTED CASE OCCURS AT THE PHYSICAL DIMENSION**, `d = 4` and `SU(3)`: extent `4` (even),
axis `0`, transverse direction `1`, lag `1` (odd). The sum-level obstruction is not a vacuous
quantification.

DERIVED: `4` is the problem's dimension and an even extent admitting an odd lag; `0` and `1` are two
distinct directions. -/
theorem oddCross_four_dim : ∃ q : Plaq 4 4, OddCross (0 : Fin 4) (1 : Fin 4) q :=
  exists_oddCross (by decide) (by norm_num) (by decide : (1 : Fin 4) ≠ (0 : Fin 4)) (by decide)

/-- **NEGATIVE CONTROL 1 — the sum-level test does not fire on a genuinely paired sum.** For a family
whose total IS a paired form, the quantity the obstruction looks at is nonnegative at every
reflection-fixed configuration, so there is no hypothesis to consume. The refutation detects the
absence of the paired form, not the presence of a reflection or of a sum. -/
theorem negctl_paired_sum_is_nonneg {γ : Type} (Θ : γ → γ) {U₀ : γ} (hfix : Θ U₀ = U₀)
    {Nc : ℕ} (X : γ → Matrix (Fin Nc) (Fin Nc) ℂ) :
    0 ≤ hsRe (X U₀) (X (Θ U₀)) := by
  rw [hfix]
  exact hsRe_self_nonneg _

/-- **NEGATIVE CONTROL 2 — the sign is carried by the witness, not by the straddling geometry.** The
same family of straddling plaquettes, evaluated at the all-identity configuration (which is also
reflection-fixed), sums to `3 · card > 0`. So `sum_re_tr_cfgSum` measures `diag(1, −1, −1)` sitting
on the fixed axis links, not the fact that the plaquettes straddle. -/
theorem negctl_sum_identity_positive {τ : Fin d} {c : Fin n} (A : Finset (Plaq d n))
    (hAne : A.Nonempty) :
    reflConf τ c (fun _ : Link d n => (1 : MassGap.SUN.SU 3)) = (fun _ => 1)
      ∧ 0 < ∑ _q ∈ A, (Matrix.trace
          ((wilsonHol (bd (d := d) (n := n)) _q (fun _ => (1 : MassGap.SUN.SU 3))
            : MassGap.SUN.SU 3) : Matrix (Fin 3) (Fin 3) ℂ)).re := by
  refine ⟨?_, ?_⟩
  · funext l
    show (if l.1 = τ then (1 : MassGap.SUN.SU 3)⁻¹ else 1) = 1
    simp
  rw [sum_re_tr_one A]
  have : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hAne
  linarith

/-- **NEGATIVE CONTROL 3 — the witness needs the EVEN extent.** `sum_val_shift_parity` is what makes
exactly one of the two fixed axis links carry `gNeg`, and it is false at odd extent: at `n = 3` the
step from coordinate `2` to coordinate `0` changes the sum by `−2`, which preserves parity. So the
parity argument is a fact about even extent, which is the case the theorem is stated in.

DERIVED: `3` is the smallest odd extent above one; `2` and `0` are the wrapping coordinate and its
image. -/
theorem negctl_parity_needs_even_extent :
    ∃ x : Site 1 3, (Even (siteSum (shift (0 : Fin 1) x)) ↔ Even (siteSum x)) := by
  refine ⟨fun _ => (2 : Fin 3), ?_⟩
  have h1 : siteSum (shift (0 : Fin 1) ((fun _ => (2 : Fin 3)) : Site 1 3)) = 0 := by decide
  have h2 : siteSum ((fun _ => (2 : Fin 3)) : Site 1 3) = 2 := by decide
  rw [h1, h2]
  exact ⟨fun _ => ⟨1, rfl⟩, fun _ => ⟨0, rfl⟩⟩

end SumControls

/-! ## Part B — the block partition at a LINK-reflection plane

The reflection constant is `c = a + a + 1`, so `2x = c` has NO solution (no fixed site, no fixed
transverse link) and `2x = c − 1` is solved by `a` and by `a + m` — the TWO fixed axis planes the
periodic extent forces. Levels are measured from `a` by `ActionSplit.lv`.

Under the reflection an AXIS coordinate at level `j` goes to level `(n − j) % n` and a TRANSVERSE one
to level `((n − j) % n + 1) % n`. That one-step offset between the two families is what a link
reflection is, and it is why the fixed set is made of axis links rather than a site-plane. -/

section OddBlocks

variable {d n : ℕ} [NeZero n]

/-- **The fixed set of a link reflection**: the AXIS links at levels `0` and `m`, whose MIDPOINTS are
the two reflection planes. `reflLink` fixes each of them (`oblkR_fixed`) and `reflConf` INVERTS each
of them (`ActionSplit.reflConf_inverts_fixed_axis_link`) — that inversion is the entire difference
from the even-lag case, and the reason `ActionSplit`'s conditional argument does not apply here.

DERIVED: `0` is the plane's own level — the level of the site `a` the levels are measured from. The
second plane is at `m`, which is a parameter, not a constant. -/
def oblkR (τ : Fin d) (a : Fin n) (m : ℕ) : Finset (Link d n) :=
  Finset.univ.filter (fun l => l.1 = τ ∧ (lv a (l.2 τ) = 0 ∨ lv a (l.2 τ) = m))

/-- The positive half: axis links strictly between the two planes, transverse links from level `1`
up to and including level `m`. The transverse levels sit one step above the axis levels, which is the
link reflection's offset.

DERIVED: `0` is the lower plane's level, excluded by `0 < ·`; `1` is the level one lattice step above
it, which is where the transverse half starts because a link reflection offsets the two families by
exactly one step. Both are read off the geometry; `m` is a parameter. -/
def oblkS (τ : Fin d) (a : Fin n) (m : ℕ) : Finset (Link d n) :=
  Finset.univ.filter (fun l =>
    if l.1 = τ then (0 < lv a (l.2 τ) ∧ lv a (l.2 τ) < m)
    else (0 < lv a (l.2 τ) ∧ lv a (l.2 τ) ≤ m))

/-- The mirror half.

DERIVED: `0` is the lower plane's level, which a transverse link at the plane belongs to on this
side because the extent is periodic. -/
def oblkT (τ : Fin d) (a : Fin n) (m : ℕ) : Finset (Link d n) :=
  Finset.univ.filter (fun l =>
    if l.1 = τ then m < lv a (l.2 τ)
    else (lv a (l.2 τ) = 0 ∨ m < lv a (l.2 τ)))

variable (τ : Fin d) (a : Fin n) (m : ℕ)

theorem mem_oblkR (l : Link d n) :
    l ∈ oblkR τ a m ↔ l.1 = τ ∧ (lv a (l.2 τ) = 0 ∨ lv a (l.2 τ) = m) := by
  rw [oblkR, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_oblkS (l : Link d n) :
    l ∈ oblkS τ a m ↔
      (if l.1 = τ then (0 < lv a (l.2 τ) ∧ lv a (l.2 τ) < m)
       else (0 < lv a (l.2 τ) ∧ lv a (l.2 τ) ≤ m)) := by
  rw [oblkS, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_oblkT (l : Link d n) :
    l ∈ oblkT τ a m ↔
      (if l.1 = τ then m < lv a (l.2 τ)
       else (lv a (l.2 τ) = 0 ∨ m < lv a (l.2 τ))) := by
  rw [oblkT, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem oblkR_axis {l : Link d n} (hl : l ∈ oblkR τ a m) : l.1 = τ :=
  ((mem_oblkR τ a m l).mp hl).1

theorem oblkS_disjoint_oblkT : Disjoint (oblkS τ a m) (oblkT τ a m) := by
  rw [Finset.disjoint_left]
  intro l hS hT
  rw [mem_oblkS] at hS
  rw [mem_oblkT] at hT
  by_cases h : l.1 = τ
  · rw [if_pos h] at hS hT; omega
  · rw [if_neg h] at hS hT; omega

theorem oblkS_disjoint_oblkR : Disjoint (oblkS τ a m) (oblkR τ a m) := by
  rw [Finset.disjoint_left]
  intro l hS hR
  obtain ⟨hax, hor⟩ := (mem_oblkR τ a m l).mp hR
  rw [mem_oblkS, if_pos hax] at hS
  omega

theorem oblkT_disjoint_oblkR : Disjoint (oblkT τ a m) (oblkR τ a m) := by
  rw [Finset.disjoint_left]
  intro l hT hR
  obtain ⟨hax, hor⟩ := (mem_oblkR τ a m l).mp hR
  rw [mem_oblkT, if_pos hax] at hT
  omega

/-- **The three blocks exhaust the links.** With the three disjointness lemmas this is the
partition. -/
theorem oblk_union_univ : oblkS τ a m ∪ oblkT τ a m ∪ oblkR τ a m = Finset.univ := by
  refine Finset.eq_univ_of_forall (fun l => ?_)
  simp only [Finset.mem_union, mem_oblkS, mem_oblkT, mem_oblkR]
  by_cases h : l.1 = τ
  · simp only [if_pos h]
    rcases Nat.lt_trichotomy (lv a (l.2 τ)) m with hlt | heq | hgt
    · rcases Nat.eq_zero_or_pos (lv a (l.2 τ)) with h0 | h0
      · exact Or.inr ⟨h, Or.inl h0⟩
      · exact Or.inl (Or.inl ⟨h0, hlt⟩)
    · exact Or.inr ⟨h, Or.inr heq⟩
    · exact Or.inl (Or.inr hgt)
  · simp only [if_neg h]
    rcases Nat.eq_zero_or_pos (lv a (l.2 τ)) with h0 | h0
    · exact Or.inl (Or.inr (Or.inl h0))
    · by_cases hle : lv a (l.2 τ) ≤ m
      · exact Or.inl (Or.inl ⟨h0, hle⟩)
      · exact Or.inl (Or.inr (Or.inr (by omega)))

/-! ### The reflection on the blocks -/

/-- **The fixed set really is fixed.** An axis link is fixed exactly when its midpoint is a plane,
which at levels `0` and `m` it is: `fcast j + fcast j = 0` for `j = 0` and for `j = m`, the latter
because `m + m = n`. -/
theorem oblkR_fixed (hm : n = 2 * m) {l : Link d n} (hl : l ∈ oblkR τ a m) :
    reflLink τ (a + a + 1) l = l := by
  obtain ⟨hax, hor⟩ := (mem_oblkR τ a m l).mp hl
  refine (reflLink_fixed_iff_axis _ l hax).mpr ?_
  have hcancel : (a + a + 1 : Fin n) - 1 = a + a := by simp
  rw [hcancel]
  have key : ∀ k : Fin n, k + k = 0 → (a + a) = (a + k) + (a + k) := by
    intro k hk
    have h2 : (a + k) + (a + k) = (a + a) + (k + k) := by abel
    rw [h2, hk, add_zero]
  have hp : l.2 τ = a + fcast n (lv a (l.2 τ)) := eq_add_lv a (l.2 τ)
  rcases hor with h0 | hmm
  · rw [hp, h0]
    exact key _ (by rw [fcast_zero, add_zero])
  · rw [hp, hmm]
    refine key _ ?_
    rw [fcast_add]
    have hmn : m + m = n := by omega
    rw [hmn, fcast_self]

/-- **The reflection carries the positive half onto the mirror.** An axis level `j` goes to `n − j`
and a transverse level `j` to `n − j + 1` modulo the extent, and the two ranges are exchanged. -/
theorem oblkS_maps_oblkT (hm : n = 2 * m) (hm0 : 0 < m) {l : Link d n} (hl : l ∈ oblkS τ a m) :
    reflLink τ (a + a + 1) l ∈ oblkT τ a m := by
  have hn : 0 < n := NeZero.pos n
  have hjn : lv a (l.2 τ) < n := lv_lt a (l.2 τ)
  have hdir : (reflLink τ (a + a + 1) l).1 = l.1 := rfl
  have hcancel : (a + a + 1 : Fin n) - 1 = a + a := by simp
  rw [mem_oblkS] at hl
  rw [mem_oblkT, hdir]
  by_cases h : l.1 = τ
  · rw [if_pos h] at hl ⊢
    have himg : (reflLink τ (a + a + 1) l).2 τ = (a + a) - l.2 τ := by
      rw [reflLink_coord_axis _ h, hcancel]
    have hinner : (n - lv a (l.2 τ)) % n = n - lv a (l.2 τ) := Nat.mod_eq_of_lt (by omega)
    rw [himg, lv_refl_site, hinner]
    omega
  · rw [if_neg h] at hl ⊢
    have himg : (reflLink τ (a + a + 1) l).2 τ = ((a + a) - l.2 τ) + 1 := by
      rw [reflLink_coord_transverse _ h]
      abel
    have hinner : (n - lv a (l.2 τ)) % n = n - lv a (l.2 τ) := Nat.mod_eq_of_lt (by omega)
    rw [himg, lv_add_one, lv_refl_site, hinner]
    rcases Nat.lt_or_ge (n - lv a (l.2 τ) + 1) n with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]
      exact Or.inr (by omega)
    · have he : n - lv a (l.2 τ) + 1 = n := by omega
      rw [he, Nat.mod_self]
      exact Or.inl rfl

/-! ### The plaquette trichotomy at a link-reflection plane

The base level `j = lv a (x τ)` and the presence of an axis direction decide everything. A plaquette
with one direction along the axis reads the axis links at level `j` and the transverse links at
levels `j` and `j + 1`; one with neither direction along the axis reads four transverse links at
level `j`. -/

/-- Plaquettes with BOTH directions along the axis: identity holonomy, zero contribution. They are
excluded from the trichotomy because they genuinely straddle — see
`odd_degenerate_axis_plaquette_straddles`. -/
def oplqDeg (τ : Fin d) : Finset (Plaq d n) :=
  Finset.univ.filter (fun q => q.1.1 = τ ∧ q.1.2 = τ)

/-- The STRADDLING plaquettes: one direction along the axis, base level on one of the two planes.

DERIVED: `0` is the level of the lower plane; the upper one is `m`, a parameter. -/
def oplqCross (τ : Fin d) (a : Fin n) (m : ℕ) : Finset (Plaq d n) :=
  Finset.univ.filter (fun q => ¬ (q.1.1 = τ ∧ q.1.2 = τ) ∧ (q.1.1 = τ ∨ q.1.2 = τ)
    ∧ (lv a (q.2 τ) = 0 ∨ lv a (q.2 τ) = m))

/-- The plaquettes reading the positive half alone.

DERIVED: `0` is the lower plane's level, excluded by `0 < ·` because a plaquette based there
straddles. -/
def oplqPlus (τ : Fin d) (a : Fin n) (m : ℕ) : Finset (Plaq d n) :=
  Finset.univ.filter (fun q => ¬ (q.1.1 = τ ∧ q.1.2 = τ) ∧ 0 < lv a (q.2 τ)
    ∧ lv a (q.2 τ) ≤ m ∧ ((q.1.1 = τ ∨ q.1.2 = τ) → lv a (q.2 τ) < m))

/-- The plaquettes reading the mirror alone.

DERIVED: `0` is the lower plane's level, which a transverse-only plaquette based there reads entirely
from the mirror side. -/
def oplqMinus (τ : Fin d) (a : Fin n) (m : ℕ) : Finset (Plaq d n) :=
  Finset.univ.filter (fun q => ¬ (q.1.1 = τ ∧ q.1.2 = τ)
    ∧ (lv a (q.2 τ) = 0 ∨ m < lv a (q.2 τ))
    ∧ ((q.1.1 = τ ∨ q.1.2 = τ) → m < lv a (q.2 τ)))

theorem mem_oplqDeg (q : Plaq d n) :
    q ∈ oplqDeg (d := d) (n := n) τ ↔ (q.1.1 = τ ∧ q.1.2 = τ) := by
  rw [oplqDeg, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_oplqCross (q : Plaq d n) :
    q ∈ oplqCross τ a m ↔ ¬ (q.1.1 = τ ∧ q.1.2 = τ) ∧ (q.1.1 = τ ∨ q.1.2 = τ)
      ∧ (lv a (q.2 τ) = 0 ∨ lv a (q.2 τ) = m) := by
  rw [oplqCross, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_oplqPlus (q : Plaq d n) :
    q ∈ oplqPlus τ a m ↔ ¬ (q.1.1 = τ ∧ q.1.2 = τ) ∧ 0 < lv a (q.2 τ)
      ∧ lv a (q.2 τ) ≤ m ∧ ((q.1.1 = τ ∨ q.1.2 = τ) → lv a (q.2 τ) < m) := by
  rw [oplqPlus, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_oplqMinus (q : Plaq d n) :
    q ∈ oplqMinus τ a m ↔ ¬ (q.1.1 = τ ∧ q.1.2 = τ)
      ∧ (lv a (q.2 τ) = 0 ∨ m < lv a (q.2 τ))
      ∧ ((q.1.1 = τ ∨ q.1.2 = τ) → m < lv a (q.2 τ)) := by
  rw [oplqMinus, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **A positive-half plaquette reads the positive half ALONE** — not `S ∪ R`, as in the even-lag
case, but `S`. At a link reflection the fixed set appears only in the straddling words. -/
theorem oplaq_links_plus (hm : n = 2 * m) (hm0 : 0 < m) {q : Plaq d n}
    (hq : q ∈ oplqPlus τ a m) : ∀ l ∈ (bd q).map Prod.fst, l ∈ oblkS τ a m := by
  obtain ⟨hdeg, h0, hle, hax⟩ := (mem_oplqPlus τ a m q).mp hq
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  have hdeg' : ¬ (μ = τ ∧ ν = τ) := hdeg
  have hax' : (μ = τ ∨ ν = τ) → lv a (x τ) < m := hax
  have h0' : 0 < lv a (x τ) := h0
  have hle' : lv a (x τ) ≤ m := hle
  have hjn : lv a (x τ) < n := lv_lt a (x τ)
  have hsucc : lv a (x τ) < m → (lv a (x τ) + 1) % n = lv a (x τ) + 1 := by
    intro hlt; exact Nat.mod_eq_of_lt (by omega)
  intro l hl
  simp only [bd, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hl
  rw [mem_oblkS]
  rcases hl with h | h | h | h <;> subst h
  · show (if μ = τ then (0 < lv a (x τ) ∧ lv a (x τ) < m)
        else (0 < lv a (x τ) ∧ lv a (x τ) ≤ m))
    by_cases hμ : μ = τ
    · rw [if_pos hμ]; exact ⟨h0', hax' (Or.inl hμ)⟩
    · rw [if_neg hμ]; exact ⟨h0', hle'⟩
  · show (if ν = τ then (0 < lv a ((shift μ x) τ) ∧ lv a ((shift μ x) τ) < m)
        else (0 < lv a ((shift μ x) τ) ∧ lv a ((shift μ x) τ) ≤ m))
    by_cases hμ : μ = τ
    · have hν : ν ≠ τ := fun hc => hdeg' ⟨hμ, hc⟩
      have hlt := hax' (Or.inl hμ)
      rw [if_neg hν, hμ, lv_shift_axis, hsucc hlt]
      omega
    · rw [lv_shift_of_ne hμ]
      by_cases hν : ν = τ
      · rw [if_pos hν]; exact ⟨h0', hax' (Or.inr hν)⟩
      · rw [if_neg hν]; exact ⟨h0', hle'⟩
  · show (if μ = τ then (0 < lv a ((shift ν x) τ) ∧ lv a ((shift ν x) τ) < m)
        else (0 < lv a ((shift ν x) τ) ∧ lv a ((shift ν x) τ) ≤ m))
    by_cases hν : ν = τ
    · have hμ : μ ≠ τ := fun hc => hdeg' ⟨hc, hν⟩
      have hlt := hax' (Or.inr hν)
      rw [if_neg hμ, hν, lv_shift_axis, hsucc hlt]
      omega
    · rw [lv_shift_of_ne hν]
      by_cases hμ : μ = τ
      · rw [if_pos hμ]; exact ⟨h0', hax' (Or.inl hμ)⟩
      · rw [if_neg hμ]; exact ⟨h0', hle'⟩
  · show (if ν = τ then (0 < lv a (x τ) ∧ lv a (x τ) < m)
        else (0 < lv a (x τ) ∧ lv a (x τ) ≤ m))
    by_cases hν : ν = τ
    · rw [if_pos hν]; exact ⟨h0', hax' (Or.inr hν)⟩
    · rw [if_neg hν]; exact ⟨h0', hle'⟩

/-- **A mirror plaquette reads the mirror ALONE.** -/
theorem oplaq_links_minus (hm : n = 2 * m) (hm0 : 0 < m) {q : Plaq d n}
    (hq : q ∈ oplqMinus τ a m) : ∀ l ∈ (bd q).map Prod.fst, l ∈ oblkT τ a m := by
  obtain ⟨hdeg, hj, hax⟩ := (mem_oplqMinus τ a m q).mp hq
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  have hdeg' : ¬ (μ = τ ∧ ν = τ) := hdeg
  have hax' : (μ = τ ∨ ν = τ) → m < lv a (x τ) := hax
  have hj' : lv a (x τ) = 0 ∨ m < lv a (x τ) := hj
  have hjn : lv a (x τ) < n := lv_lt a (x τ)
  have hsucc : (lv a (x τ) + 1) % n = 0 ∨ (lv a (x τ) + 1) % n = lv a (x τ) + 1 := by
    rcases Nat.lt_or_ge (lv a (x τ) + 1) n with h | h
    · exact Or.inr (Nat.mod_eq_of_lt h)
    · have he : lv a (x τ) + 1 = n := by omega
      exact Or.inl (by rw [he, Nat.mod_self])
  intro l hl
  simp only [bd, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hl
  rw [mem_oblkT]
  rcases hl with h | h | h | h <;> subst h
  · show (if μ = τ then m < lv a (x τ) else (lv a (x τ) = 0 ∨ m < lv a (x τ)))
    by_cases hμ : μ = τ
    · rw [if_pos hμ]; exact hax' (Or.inl hμ)
    · rw [if_neg hμ]; exact hj'
  · show (if ν = τ then m < lv a ((shift μ x) τ)
        else (lv a ((shift μ x) τ) = 0 ∨ m < lv a ((shift μ x) τ)))
    by_cases hμ : μ = τ
    · have hν : ν ≠ τ := fun hc => hdeg' ⟨hμ, hc⟩
      have hgt := hax' (Or.inl hμ)
      rw [if_neg hν, hμ, lv_shift_axis]
      rcases hsucc with h | h <;> rw [h] <;> omega
    · rw [lv_shift_of_ne hμ]
      by_cases hν : ν = τ
      · rw [if_pos hν]; exact hax' (Or.inr hν)
      · rw [if_neg hν]; exact hj'
  · show (if μ = τ then m < lv a ((shift ν x) τ)
        else (lv a ((shift ν x) τ) = 0 ∨ m < lv a ((shift ν x) τ)))
    by_cases hν : ν = τ
    · have hμ : μ ≠ τ := fun hc => hdeg' ⟨hc, hν⟩
      have hgt := hax' (Or.inr hν)
      rw [if_neg hμ, hν, lv_shift_axis]
      rcases hsucc with h | h <;> rw [h] <;> omega
    · rw [lv_shift_of_ne hν]
      by_cases hμ : μ = τ
      · rw [if_pos hμ]; exact hax' (Or.inl hμ)
      · rw [if_neg hμ]; exact hj'
  · show (if ν = τ then m < lv a (x τ) else (lv a (x τ) = 0 ∨ m < lv a (x τ)))
    by_cases hν : ν = τ
    · rw [if_pos hν]; exact hax' (Or.inr hν)
    · rw [if_neg hν]; exact hj'

/-- **A straddling plaquette is exactly an `OddCross` plaquette of the reflection `a + a + 1`** — the
predicate Part A's obstruction is stated over. The class the partition isolates and the class the
witness defeats are the same class. -/
theorem oplqCross_oddCross (hm : n = 2 * m) {q : Plaq d n} (hq : q ∈ oplqCross τ a m) :
    OddCross τ (a + a + 1) q := by
  obtain ⟨hdeg, hax, hlev⟩ := (mem_oplqCross τ a m q).mp hq
  refine ⟨?_, hax, ?_⟩
  · rcases hax with h | h
    · exact fun hc => hdeg ⟨h, hc ▸ h⟩
    · exact fun hc => hdeg ⟨hc ▸ h, h⟩
  · refine oblkR_fixed τ a m hm ?_
    rw [mem_oblkR]
    exact ⟨rfl, hlev⟩

/-- **THE TRICHOTOMY.** Every non-degenerate plaquette reads the positive half alone, reads the
mirror alone, or STRADDLES — and the straddling ones are exactly those with one direction along the
axis and a base site on one of the two planes.

This is `ActionSplit.plaq_side` at a link-reflection plane, and it is sharper there than here in one
respect and blunter in another: the one-sided cases do not touch the fixed set at all, but a third
class survives, which the even-lag geometry does not have. -/
theorem oplaq_side (hm : n = 2 * m) (hm0 : 0 < m) {q : Plaq d n}
    (hdeg : ¬ (q.1.1 = τ ∧ q.1.2 = τ)) :
    (∀ l ∈ (bd q).map Prod.fst, l ∈ oblkS τ a m)
      ∨ (∀ l ∈ (bd q).map Prod.fst, l ∈ oblkT τ a m)
      ∨ OddCross τ (a + a + 1) q := by
  by_cases hax : q.1.1 = τ ∨ q.1.2 = τ
  · rcases Nat.lt_trichotomy (lv a (q.2 τ)) m with hlt | heq | hgt
    · rcases Nat.eq_zero_or_pos (lv a (q.2 τ)) with h0 | h0
      · exact Or.inr (Or.inr (oplqCross_oddCross τ a m hm
          ((mem_oplqCross τ a m q).mpr ⟨hdeg, hax, Or.inl h0⟩)))
      · exact Or.inl (oplaq_links_plus τ a m hm hm0
          ((mem_oplqPlus τ a m q).mpr ⟨hdeg, h0, le_of_lt hlt, fun _ => hlt⟩))
    · exact Or.inr (Or.inr (oplqCross_oddCross τ a m hm
        ((mem_oplqCross τ a m q).mpr ⟨hdeg, hax, Or.inr heq⟩)))
    · exact Or.inr (Or.inl (oplaq_links_minus τ a m hm hm0
        ((mem_oplqMinus τ a m q).mpr ⟨hdeg, Or.inr hgt, fun _ => hgt⟩)))
  · rcases Nat.eq_zero_or_pos (lv a (q.2 τ)) with h0 | h0
    · exact Or.inr (Or.inl (oplaq_links_minus τ a m hm hm0
        ((mem_oplqMinus τ a m q).mpr ⟨hdeg, Or.inl h0, fun h => absurd h hax⟩)))
    · by_cases hle : lv a (q.2 τ) ≤ m
      · exact Or.inl (oplaq_links_plus τ a m hm hm0
          ((mem_oplqPlus τ a m q).mpr ⟨hdeg, h0, hle, fun h => absurd h hax⟩))
      · exact Or.inr (Or.inl (oplaq_links_minus τ a m hm hm0
          ((mem_oplqMinus τ a m q).mpr ⟨hdeg, Or.inr (by omega), fun h => absurd h hax⟩)))

/-- **THE ACTION SPLITS FOUR WAYS.** The four classes partition the plaquettes, so any plaquette sum
— the Wilson action among them — is the degenerate part (which vanishes), plus the positive half's
part, plus the mirror's part, plus the straddling part. -/
theorem sum_oplaq_split {M : Type} [AddCommMonoid M] (f : Plaq d n → M) :
    ∑ q, f q = ((∑ q ∈ oplqDeg (d := d) (n := n) τ, f q) + (∑ q ∈ oplqCross τ a m, f q))
      + ((∑ q ∈ oplqPlus τ a m, f q) + (∑ q ∈ oplqMinus τ a m, f q)) := by
  have hdc : Disjoint (oplqDeg (d := d) (n := n) τ) (oplqCross τ a m) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    exact ((mem_oplqCross τ a m q).mp h2).1 ((mem_oplqDeg τ q).mp h1)
  have hpm : Disjoint (oplqPlus (d := d) (n := n) τ a m) (oplqMinus τ a m) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    obtain ⟨-, h0, hle, hax⟩ := (mem_oplqPlus τ a m q).mp h1
    obtain ⟨-, hj, hax'⟩ := (mem_oplqMinus τ a m q).mp h2
    by_cases h : q.1.1 = τ ∨ q.1.2 = τ
    · have hlt := hax h
      have hgt := hax' h
      omega
    · omega
  have hcross : Disjoint (oplqDeg (d := d) (n := n) τ ∪ oplqCross τ a m)
      (oplqPlus τ a m ∪ oplqMinus τ a m) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    rcases Finset.mem_union.mp h1 with hd | hz <;> rcases Finset.mem_union.mp h2 with hp | hn
    · exact ((mem_oplqPlus τ a m q).mp hp).1 ((mem_oplqDeg τ q).mp hd)
    · exact ((mem_oplqMinus τ a m q).mp hn).1 ((mem_oplqDeg τ q).mp hd)
    · obtain ⟨-, hax, hlev⟩ := (mem_oplqCross τ a m q).mp hz
      obtain ⟨-, h0, hle, hax'⟩ := (mem_oplqPlus τ a m q).mp hp
      have hlt := hax' hax
      omega
    · obtain ⟨-, hax, hlev⟩ := (mem_oplqCross τ a m q).mp hz
      obtain ⟨-, hj, hax'⟩ := (mem_oplqMinus τ a m q).mp hn
      have hgt := hax' hax
      omega
  have huniv : (oplqDeg (d := d) (n := n) τ ∪ oplqCross τ a m)
      ∪ (oplqPlus τ a m ∪ oplqMinus τ a m) = Finset.univ := by
    refine Finset.eq_univ_of_forall (fun q => ?_)
    simp only [Finset.mem_union, mem_oplqDeg, mem_oplqCross, mem_oplqPlus, mem_oplqMinus]
    by_cases hdeg : q.1.1 = τ ∧ q.1.2 = τ
    · exact Or.inl (Or.inl hdeg)
    · by_cases hax : q.1.1 = τ ∨ q.1.2 = τ
      · rcases Nat.lt_trichotomy (lv a (q.2 τ)) m with hlt | heq | hgt
        · rcases Nat.eq_zero_or_pos (lv a (q.2 τ)) with h0 | h0
          · exact Or.inl (Or.inr ⟨hdeg, hax, Or.inl h0⟩)
          · exact Or.inr (Or.inl ⟨hdeg, h0, le_of_lt hlt, fun _ => hlt⟩)
        · exact Or.inl (Or.inr ⟨hdeg, hax, Or.inr heq⟩)
        · exact Or.inr (Or.inr ⟨hdeg, Or.inr hgt, fun _ => hgt⟩)
      · rcases Nat.eq_zero_or_pos (lv a (q.2 τ)) with h0 | h0
        · exact Or.inr (Or.inr ⟨hdeg, Or.inl h0, fun h => absurd h hax⟩)
        · by_cases hle : lv a (q.2 τ) ≤ m
          · exact Or.inr (Or.inl ⟨hdeg, h0, hle, fun h => absurd h hax⟩)
          · exact Or.inr (Or.inr ⟨hdeg, Or.inr (by omega), fun h => absurd h hax⟩)
  rw [← huniv, Finset.sum_union hcross, Finset.sum_union hdc, Finset.sum_union hpm]

/-- **The degenerate class contributes nothing** — the boundary word retraces itself. -/
theorem sum_oplqDeg_zero {N : ℕ} (hN : N ≠ 0) (U : Link d n → MassGap.SUN.SU N) :
    ∑ q ∈ oplqDeg (d := d) (n := n) τ,
      MassGap.WilsonAction.wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) = 0 := by
  refine Finset.sum_eq_zero (fun q hq => ?_)
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  obtain ⟨h1, h2⟩ := (mem_oplqDeg τ _).mp hq
  have hνμ : ν = μ := by
    show ν = μ
    rw [show ν = τ from h2, show μ = τ from h1]
  rw [show (((μ, ν), x) : Plaq d n) = ((μ, μ), x) by rw [hνμ], hol_diag_one,
    MassGap.WilsonAction.wilsonDensity_one hN]

end OddBlocks

/-! ### Negative controls for Part B -/

section BlockControls

variable {d n : ℕ} [NeZero n]

/-- **NEGATIVE CONTROL — a straddling plaquette genuinely straddles.** Isolating `oplqCross` is not
bookkeeping convenience: such a plaquette reads a link of `oblkS` AND a link of `oblkT`, so it lies
in neither half however the halves are read, and no rearrangement of the partition removes it.

At base level `0` its two transverse links sit at levels `0` (mirror) and `1` (positive half); at
base level `m` they sit at levels `m` (positive half) and `m + 1` (mirror, or level `0` when the
extent is `2`). -/
theorem oplqCross_reads_both (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m) (hm0 : 0 < m)
    {q : Plaq d n} (hq : q ∈ oplqCross τ a m) :
    (∃ l ∈ (bd q).map Prod.fst, l ∈ oblkS τ a m)
      ∧ (∃ l ∈ (bd q).map Prod.fst, l ∈ oblkT τ a m) := by
  have hn : 0 < n := NeZero.pos n
  obtain ⟨hdeg, hax, hlev⟩ := (mem_oplqCross τ a m q).mp hq
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  have hdeg' : ¬ (μ = τ ∧ ν = τ) := hdeg
  have hlev' : lv a (x τ) = 0 ∨ lv a (x τ) = m := hlev
  have hcase : (μ = τ ∧ ν ≠ τ) ∨ (ν = τ ∧ μ ≠ τ) := by
    rcases hax with h | h
    · exact Or.inl ⟨h, fun hc => hdeg' ⟨h, hc⟩⟩
    · exact Or.inr ⟨h, fun hc => hdeg' ⟨hc, h⟩⟩
  have hkey : ∀ ρ σ : Fin d, ρ ≠ τ → σ = τ →
      (((ρ, shift σ x) : Link d n) ∈ oblkS τ a m ∧ ((ρ, x) : Link d n) ∈ oblkT τ a m)
        ∨ (((ρ, x) : Link d n) ∈ oblkS τ a m
          ∧ ((ρ, shift σ x) : Link d n) ∈ oblkT τ a m) := by
    intro ρ σ hρ hσ
    rcases hlev' with h0 | hmm
    · refine Or.inl ⟨?_, ?_⟩
      · rw [mem_oblkS, if_neg hρ]
        show 0 < lv a ((shift σ x) τ) ∧ lv a ((shift σ x) τ) ≤ m
        rw [hσ, lv_shift_axis, h0, Nat.mod_eq_of_lt (by omega)]
        omega
      · rw [mem_oblkT, if_neg hρ]
        exact Or.inl h0
    · refine Or.inr ⟨?_, ?_⟩
      · rw [mem_oblkS, if_neg hρ]
        show 0 < lv a (x τ) ∧ lv a (x τ) ≤ m
        omega
      · rw [mem_oblkT, if_neg hρ]
        show lv a ((shift σ x) τ) = 0 ∨ m < lv a ((shift σ x) τ)
        rw [hσ, lv_shift_axis, hmm]
        rcases Nat.lt_or_ge (m + 1) n with hlt | hge
        · exact Or.inr (by rw [Nat.mod_eq_of_lt hlt]; omega)
        · have he : m + 1 = n := by omega
          exact Or.inl (by rw [he, Nat.mod_self])
  rcases hcase with ⟨hμ, hν⟩ | ⟨hν, hμ⟩
  · rcases hkey ν μ hν hμ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨⟨(ν, shift μ x), by simp [bd], h1⟩, ⟨(ν, x), by simp [bd], h2⟩⟩
    · exact ⟨⟨(ν, x), by simp [bd], h1⟩, ⟨(ν, shift μ x), by simp [bd], h2⟩⟩
  · rcases hkey μ ν hμ hν with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨⟨(μ, shift ν x), by simp [bd], h1⟩, ⟨(μ, x), by simp [bd], h2⟩⟩
    · exact ⟨⟨(μ, x), by simp [bd], h1⟩, ⟨(μ, shift ν x), by simp [bd], h2⟩⟩

/-- **NEGATIVE CONTROL — the degenerate class cannot be folded into the trichotomy.** The plaquette
with BOTH directions along the axis, based at level `m − 1`, reads an axis link at level `m − 1`
(positive half) and one at level `m` (the fixed set), so it is in neither `oblkS` alone nor `oblkT`
alone; and it has no transverse direction, so it is not `OddCross` either. Its holonomy is the
identity (`sum_oplqDeg_zero`), which is why excluding it costs nothing.

DERIVED: `m − 1` is the level one step below the upper plane; `2 ≤ m` is what makes that level
strictly inside the positive half rather than the lower plane itself. -/
theorem odd_degenerate_axis_plaquette_straddles (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm2 : 2 ≤ m) :
    ∃ q : Plaq d n, q.1.1 = τ ∧ q.1.2 = τ
      ∧ ¬ ((∀ l ∈ (bd q).map Prod.fst, l ∈ oblkS τ a m)
        ∨ (∀ l ∈ (bd q).map Prod.fst, l ∈ oblkT τ a m)
        ∨ OddCross τ (a + a + 1) q) := by
  have hn : 0 < n := NeZero.pos n
  refine ⟨((τ, τ), Function.update (fun _ => a) τ (a + fcast n (m - 1))), rfl, rfl, ?_⟩
  set x : Site d n := Function.update (fun _ => a) τ (a + fcast n (m - 1)) with hx
  have hxτ : x τ = a + fcast n (m - 1) := by rw [hx, Function.update_self]
  have hlev : lv a (x τ) = m - 1 := by
    rw [hxτ, lv_add_fcast a _ (by omega)]
  have hlevU : lv a ((shift τ x) τ) = m := by
    rw [lv_shift_axis, hlev]
    have hstep : m - 1 + 1 = m := by omega
    rw [hstep, Nat.mod_eq_of_lt (by omega)]
  have hlev1 : lv a (((τ, x) : Link d n).2 τ) = m - 1 := hlev
  have hlev2 : lv a (((τ, shift τ x) : Link d n).2 τ) = m := hlevU
  have hmem1 : ((τ, x) : Link d n) ∈ (bd (((τ, τ), x) : Plaq d n)).map Prod.fst := by
    simp [bd]
  have hmem2 : ((τ, shift τ x) : Link d n)
      ∈ (bd (((τ, τ), x) : Plaq d n)).map Prod.fst := by
    simp [bd]
  have hR2 : ((τ, shift τ x) : Link d n) ∈ oblkR τ a m := by
    rw [mem_oblkR]
    exact ⟨rfl, Or.inr hlev2⟩
  have hS1 : ((τ, x) : Link d n) ∈ oblkS τ a m := by
    rw [mem_oblkS, if_pos rfl]
    exact ⟨by omega, by omega⟩
  rintro (hS | hT | hC)
  · exact (Finset.disjoint_left.mp (oblkS_disjoint_oblkR τ a m)) (hS _ hmem2) hR2
  · exact (Finset.disjoint_left.mp (oblkS_disjoint_oblkT τ a m)) hS1 (hT _ hmem1)
  · exact hC.1 rfl

end BlockControls

section AuditB
#print axioms mem_oblkR
#print axioms oblk_union_univ
#print axioms oblkS_disjoint_oblkT
#print axioms oblkS_disjoint_oblkR
#print axioms oblkT_disjoint_oblkR
#print axioms oblkR_fixed
#print axioms oblkS_maps_oblkT
#print axioms oplaq_links_plus
#print axioms oplaq_links_minus
#print axioms oplqCross_oddCross
#print axioms oplaq_side
#print axioms sum_oplaq_split
#print axioms sum_oplqDeg_zero
#print axioms oplqCross_reads_both
#print axioms odd_degenerate_axis_plaquette_straddles
end AuditB


/-! ## Part C — the DIRECT SUM, which is what a sum of straddling plaquettes needs

`CrossingIntegration.hsRe_conj` is one matrix pair under one gauge pair, and its own docstring says
the direct-sum version is not proved there. `wilson_crossing_pairing_nonneg` reads a SINGLE word `X`,
so aggregating several straddling plaquettes means making `X` block-diagonal. Two facts are then
needed and are proved here:

* the cross form of two block-diagonal matrices is the SUM of the blocks' cross forms
  (`hsReG_blockDiagonal`); and
* it is invariant when each block is conjugated by ITS OWN gauge pair (`hsRe_dsum_conj`) — which is
  the form the lattice supplies, since each straddling plaquette carries its own two plane links.

`hsRe_blockDiagonal_fin` transports the identity to a `Fin`-indexed matrix, which is the type
`wilson_crossing_pairing_nonneg` actually takes. -/

section DirectSum

/-- The Wilson cross form over an arbitrary finite index. `CharacterExpansion.hsRe` is this at
`ι = Fin N`; the generality is only so that a block-diagonal index `Fin N × K` can be used before it
is transported to a `Fin`. -/
noncomputable def hsReG {ι : Type} [Fintype ι] (A B : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (A * Matrix.conjTranspose B)).re

theorem hsReG_eq_hsRe {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) : hsReG A B = hsRe A B := rfl

/-- **Relabelling the index does not move the cross form.** -/
theorem hsReG_submatrix_equiv {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι)
    (A B : Matrix ι ι ℂ) :
    hsReG (A.submatrix e e) (B.submatrix e e) = hsReG A B := by
  have htr : ∀ M : Matrix ι ι ℂ, Matrix.trace (M.submatrix (e : κ → ι) (e : κ → ι))
      = Matrix.trace M := by
    intro M
    show ∑ i : κ, M (e i) (e i) = ∑ j : ι, M j j
    exact Fintype.sum_equiv e _ _ (fun i => rfl)
  unfold hsReG
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, htr]

/-- **THE CROSS FORM OF TWO DIRECT SUMS IS THE SUM OF THE CROSS FORMS.**

`blockDiagonal X * (blockDiagonal Y)ᴴ` is block-diagonal with blocks `X k * (Y k)ᴴ`, and the trace of
a block-diagonal matrix is the sum of the blocks' traces. This is the whole reason a SUM of
straddling plaquettes can be read as ONE cross form.

DERIVED: no numeral. -/
theorem hsReG_blockDiagonal {K : Type} [Fintype K] [DecidableEq K] {N : ℕ}
    (X Y : K → Matrix (Fin N) (Fin N) ℂ) :
    hsReG (Matrix.blockDiagonal X) (Matrix.blockDiagonal Y) = ∑ k, hsRe (X k) (Y k) := by
  unfold hsReG
  rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul, Matrix.trace_blockDiagonal,
    Complex.re_sum]
  rfl

/-- **`hsRe_conj` FOR A WHOLE FAMILY AT ONCE** — each block conjugated by its OWN gauge pair.

This is the direct-sum form `CrossingIntegration.hsRe_conj`'s docstring names and does not prove. On
the lattice the family is indexed by the straddling plaquettes and each one's gauge pair is the two
fixed axis links it reads, so the per-block pairs are genuinely different and the one-pair version
does not suffice. -/
theorem hsRe_dsum_conj {K : Type} [Fintype K] [DecidableEq K] {N : ℕ}
    (g h a b : K → MassGap.SUN.SU N) :
    hsReG (Matrix.blockDiagonal (fun k => ((g k * a k * (h k)⁻¹ : MassGap.SUN.SU N)
          : Matrix (Fin N) (Fin N) ℂ)))
        (Matrix.blockDiagonal (fun k => ((g k * b k * (h k)⁻¹ : MassGap.SUN.SU N)
          : Matrix (Fin N) (Fin N) ℂ)))
      = hsReG (Matrix.blockDiagonal (fun k => ((a k : MassGap.SUN.SU N)
            : Matrix (Fin N) (Fin N) ℂ)))
          (Matrix.blockDiagonal (fun k => ((b k : MassGap.SUN.SU N)
            : Matrix (Fin N) (Fin N) ℂ))) := by
  rw [hsReG_blockDiagonal, hsReG_blockDiagonal]
  exact Finset.sum_congr rfl (fun k _ => hsRe_conj (g k) (h k) (a k) (b k))

/-- **The same identity for a `Fin`-indexed block-diagonal matrix**, which is the type
`CrossingIntegration.wilson_crossing_pairing_nonneg` takes for its word `X`. The relabelling is any
bijection `Fin (card (Fin N × K)) ≃ Fin N × K` and the cross form does not see it. -/
theorem hsRe_blockDiagonal_fin {K : Type} [Fintype K] [DecidableEq K] {N : ℕ}
    (X Y : K → Matrix (Fin N) (Fin N) ℂ) :
    hsRe ((Matrix.blockDiagonal X).submatrix
          (Fintype.equivFin (Fin N × K)).symm (Fintype.equivFin (Fin N × K)).symm)
        ((Matrix.blockDiagonal Y).submatrix
          (Fintype.equivFin (Fin N × K)).symm (Fintype.equivFin (Fin N × K)).symm)
      = ∑ k, hsRe (X k) (Y k) := by
  rw [← hsReG_eq_hsRe, hsReG_submatrix_equiv, hsReG_blockDiagonal]

/-- **NEGATIVE CONTROL — the two-sided shape is load-bearing in the direct sum too.** Multiplying one
argument's block by a group element and not the other's changes the cross form: with a single block
it moves `3` to `−1`. So `hsRe_dsum_conj` is a statement about CONJUGATION, not about direct sums
absorbing arbitrary group elements.

DERIVED: `3` is `Re tr 1` in `SU(3)` and `−1` is `Re tr diag(1, −1, −1)`; both are computed. -/
theorem negctl_dsum_one_sided_not_invariant :
    hsReG (Matrix.blockDiagonal
          (fun _ : Fin 1 => ((gNeg : MassGap.SUN.SU 3) : Matrix (Fin 3) (Fin 3) ℂ)))
        (Matrix.blockDiagonal
          (fun _ : Fin 1 => ((1 : MassGap.SUN.SU 3) : Matrix (Fin 3) (Fin 3) ℂ)))
      ≠ hsReG (Matrix.blockDiagonal
          (fun _ : Fin 1 => ((1 : MassGap.SUN.SU 3) : Matrix (Fin 3) (Fin 3) ℂ)))
        (Matrix.blockDiagonal
          (fun _ : Fin 1 => ((1 : MassGap.SUN.SU 3) : Matrix (Fin 3) (Fin 3) ℂ))) := by
  rw [hsReG_blockDiagonal, hsReG_blockDiagonal]
  have hL : hsRe ((gNeg : MassGap.SUN.SU 3) : Matrix (Fin 3) (Fin 3) ℂ)
      ((1 : MassGap.SUN.SU 3) : Matrix (Fin 3) (Fin 3) ℂ) = -1 := by
    rw [hsRe_coe_eq, inv_one, mul_one, trace_gNeg]
  have hR : hsRe ((1 : MassGap.SUN.SU 3) : Matrix (Fin 3) (Fin 3) ℂ)
      ((1 : MassGap.SUN.SU 3) : Matrix (Fin 3) (Fin 3) ℂ) = 3 := by
    rw [hsRe_coe_eq, inv_one, mul_one, Submonoid.coe_one, Matrix.trace_one]
    norm_num
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hL),
    Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hR)]
  norm_num

end DirectSum

/-! ## Part D — the straddling word IS the gauge-transformed cross form

A straddling plaquette reads two links of the fixed set and two transverse links, one from each half.
Written out, its boundary word is

    g · F · g'⁻¹ · F̄⁻¹

with `g, g'` the two fixed axis links and `F, F̄` the two transverse ones. That is exactly
`hsRe (g F g'⁻¹) F̄` — the Wilson cross form of one half's link against the other's, with the plane
links absorbed into one argument as a GAUGE. `CrossingIntegration`'s crossing integration consumes
that shape and nothing else about the geometry. -/

section CrossWord

variable {d n N : ℕ} [NeZero n]

/-- **The straddling word, written out** at `((τ, ν), x)`. Nothing is assumed: this is the boundary
word of `WilsonHypercubic.bd` regrouped. -/
theorem cross_word_left (τ ν : Fin d) (x : Site d n) (U : Link d n → MassGap.SUN.SU N) :
    wilsonHol (bd (d := d) (n := n)) (((τ, ν), x) : Plaq d n) U
      = (U (τ, x) * U (ν, shift τ x) * (U (τ, shift ν x))⁻¹) * (U (ν, x))⁻¹ := by
  simp [wilsonHol, bd, mul_assoc]

/-- **The straddling word at the reversed orientation** `((ν, τ), x)`, which is the inverse of the
other and therefore has the same `Re tr`. -/
theorem cross_word_right (τ ν : Fin d) (x : Site d n) (U : Link d n → MassGap.SUN.SU N) :
    wilsonHol (bd (d := d) (n := n)) (((ν, τ), x) : Plaq d n) U
      = (U (ν, x) * U (τ, shift ν x) * (U (ν, shift τ x))⁻¹) * (U (τ, x))⁻¹ := by
  simp [wilsonHol, bd, mul_assoc]

/-- **THE STRADDLING WORD'S `Re tr` IS THE GAUGE-TRANSFORMED WILSON CROSS FORM.**

`U (τ, x)` and `U (τ, shift ν x)` are the plaquette's two FIXED AXIS links — the plane gauge — and
they act on the transverse link `U (ν, shift τ x)` exactly as a gauge field acts on a link variable,
`F ↦ g F g'⁻¹`. The word's real trace is the cross form of that gauge-transformed link against the
transverse link on the other side of the plane.

This is the identification `CrossingIntegration` states as its remaining task and does not perform:
its `hsRe (X (act g x)) (X y)` is this, with `act` the gauge action of the fixed axis links.

DERIVED: no numeral. -/
theorem hsRe_cross_word_left (τ ν : Fin d) (x : Site d n) (U : Link d n → MassGap.SUN.SU N) :
    (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) (((τ, ν), x) : Plaq d n) U
        : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re
      = hsRe (((U (τ, x) * U (ν, shift τ x) * (U (τ, shift ν x))⁻¹ : MassGap.SUN.SU N)
            : Matrix (Fin N) (Fin N) ℂ))
          ((U (ν, x) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  rw [hsRe_coe_eq, cross_word_left]

/-- The same at the reversed orientation: the gauge is the same pair, and the two transverse links
exchange roles. -/
theorem hsRe_cross_word_right (τ ν : Fin d) (x : Site d n) (U : Link d n → MassGap.SUN.SU N) :
    (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) (((ν, τ), x) : Plaq d n) U
        : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re
      = hsRe (((U (ν, x) * U (τ, shift ν x) * (U (ν, shift τ x))⁻¹ : MassGap.SUN.SU N)
            : Matrix (Fin N) (Fin N) ℂ))
          ((U (τ, x) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  rw [hsRe_coe_eq, cross_word_right]

/-- **THE STRADDLING FACTOR IS ONE CROSS FORM OF TWO BLOCK-DIAGONAL WORDS.**

Summing `hsRe_cross_word_left` over a family of straddling plaquettes and folding the sum into a
single direct sum (`hsReG_blockDiagonal`) gives the aggregated form: the whole straddling part of the
Wilson action is `hsReG` of one block-diagonal matrix — the gauge-transformed positive-half links —
against another — the mirror's links. That is the single `X` the crossing integration reads.

Here the family is presented by its base sites `w : K → Site d n` and transverse directions
`v : K → Fin d`, which is how `oplqCross` enumerates it. -/
theorem sum_hsRe_cross_word {K : Type} [Fintype K] [DecidableEq K] (τ : Fin d)
    (v : K → Fin d) (w : K → Site d n) (U : Link d n → MassGap.SUN.SU N) :
    (∑ k, (Matrix.trace ((wilsonHol (bd (d := d) (n := n))
        (((τ, v k), w k) : Plaq d n) U : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re)
      = hsReG
          (Matrix.blockDiagonal (fun k => ((U (τ, w k) * U (v k, shift τ (w k))
              * (U (τ, shift (v k) (w k)))⁻¹ : MassGap.SUN.SU N)
            : Matrix (Fin N) (Fin N) ℂ)))
          (Matrix.blockDiagonal (fun k => ((U (v k, w k) : MassGap.SUN.SU N)
            : Matrix (Fin N) (Fin N) ℂ))) := by
  rw [hsReG_blockDiagonal]
  exact Finset.sum_congr rfl (fun k _ => hsRe_cross_word_left τ (v k) (w k) U)

/-- **AND THE AGGREGATED FORM IS GAUGE-INVARIANT.** Replacing the plane links by `p · g` on the left
of each block and `q · h` on the right leaves the aggregated cross form alone, block by block. This
is `hsRe_dsum_conj` pointed at the lattice's own family: each straddling plaquette carries its own
pair of fixed axis links, so the per-block pairs really are different and the single-pair statement
would not do.

DERIVED: no numeral. -/
theorem sum_hsRe_cross_word_gauge_invariant {K : Type} [Fintype K] [DecidableEq K]
    (g h a b : K → MassGap.SUN.SU N) :
    hsReG (Matrix.blockDiagonal (fun k => ((g k * a k * (h k)⁻¹ : MassGap.SUN.SU N)
          : Matrix (Fin N) (Fin N) ℂ)))
        (Matrix.blockDiagonal (fun k => ((g k * b k * (h k)⁻¹ : MassGap.SUN.SU N)
          : Matrix (Fin N) (Fin N) ℂ)))
      = hsReG (Matrix.blockDiagonal (fun k => ((a k : MassGap.SUN.SU N)
            : Matrix (Fin N) (Fin N) ℂ)))
          (Matrix.blockDiagonal (fun k => ((b k : MassGap.SUN.SU N)
            : Matrix (Fin N) (Fin N) ℂ))) :=
  hsRe_dsum_conj g h a b

end CrossWord

/-! ### The two planes present the gauge with OPPOSITE handedness

A link reflection has TWO fixed planes, at levels `0` and `m`, and the straddling plaquettes at the
two of them do NOT present the same side to the positive half. At level `0` the transverse link the
positive half owns is `(ν, x + τ̂)` and the gauge acts on it as `F ↦ g · F · h⁻¹`; at level `m` the
positive half owns `(ν, x)` instead, and the SAME word then reads `F ↦ g⁻¹ · F · h`.

`cross_word_both_handednesses` is that statement: one word, two readings, gauges inverse to each
other. It matters because `CrossingIntegration.wilson_crossing_pairing_nonneg` takes a single group
action `act : Γ → Ω → Ω` with `act h (act g x) = act (h * g) x`, and `g · F · h⁻¹` on one plane
together with `g⁻¹ · F · h` on the other is not one such action on a non-abelian group — the two
compose in opposite orders. Making it one requires reparametrising the plane variables of ONE of the
two planes by inversion, which `Reflect.isInvInvariant_probHaar` licenses inside the integral and
which is NOT performed here. -/

section Handedness

variable {N : ℕ}

/-- **`Re tr` does not see inversion on `SU(N)`** — the inverse is the conjugate transpose and the
trace of a conjugate transpose is the conjugate of the trace. -/
theorem re_trace_inv (u : MassGap.SUN.SU N) :
    (Matrix.trace (((u⁻¹ : MassGap.SUN.SU N)) : Matrix (Fin N) (Fin N) ℂ)).re
      = (Matrix.trace ((u : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re := by
  rw [coe_inv_eq_conjTranspose, Matrix.trace_conjTranspose]
  simp

/-- **Trace cyclicity on `SU(N)`**, in the coerced form the plaquette words come in. -/
theorem trace_su_mul_comm (X Y : MassGap.SUN.SU N) :
    Matrix.trace (((X * Y : MassGap.SUN.SU N)) : Matrix (Fin N) (Fin N) ℂ)
      = Matrix.trace (((Y * X : MassGap.SUN.SU N)) : Matrix (Fin N) (Fin N) ℂ) := by
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Matrix.trace_mul_comm]

/-- **The same word read from the other side.** `Re tr (g · a · h⁻¹ · b⁻¹)` is the cross form of `a`
against `b` gauged by `(g, h)`, and equally the cross form of `b` against `a` gauged by
`(g⁻¹, h⁻¹)`. The two readings differ by inverting the gauge. -/
theorem re_trace_flip (g h a b : MassGap.SUN.SU N) :
    (Matrix.trace ((((g * a * h⁻¹) * b⁻¹ : MassGap.SUN.SU N))
        : Matrix (Fin N) (Fin N) ℂ)).re
      = hsRe (((g⁻¹ * b * h : MassGap.SUN.SU N)) : Matrix (Fin N) (Fin N) ℂ)
          ((a : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  rw [hsRe_coe_eq]
  have h1 : (((g * a * h⁻¹) * b⁻¹)⁻¹ : MassGap.SUN.SU N) = (b * h * a⁻¹) * g⁻¹ := by group
  have h2 : ((g⁻¹ * (b * h * a⁻¹)) : MassGap.SUN.SU N) = (g⁻¹ * b * h) * a⁻¹ := by group
  calc (Matrix.trace ((((g * a * h⁻¹) * b⁻¹ : MassGap.SUN.SU N))
          : Matrix (Fin N) (Fin N) ℂ)).re
      = (Matrix.trace (((((g * a * h⁻¹) * b⁻¹)⁻¹ : MassGap.SUN.SU N))
          : Matrix (Fin N) (Fin N) ℂ)).re := (re_trace_inv _).symm
    _ = (Matrix.trace ((((b * h * a⁻¹) * g⁻¹ : MassGap.SUN.SU N))
          : Matrix (Fin N) (Fin N) ℂ)).re := by rw [h1]
    _ = (Matrix.trace (((g⁻¹ * (b * h * a⁻¹) : MassGap.SUN.SU N))
          : Matrix (Fin N) (Fin N) ℂ)).re := by rw [trace_su_mul_comm]
    _ = (Matrix.trace (((((g⁻¹ * b * h) * a⁻¹) : MassGap.SUN.SU N))
          : Matrix (Fin N) (Fin N) ℂ)).re := by rw [h2]

end Handedness

section HandednessLattice

variable {d n N : ℕ} [NeZero n]

/-- **ONE STRADDLING WORD, TWO GAUGE READINGS, AND THE GAUGES ARE INVERSE.**

Which reading the action split needs is decided by WHICH transverse link the positive half owns, and
that differs between the plane at level `0` and the plane at level `m` (`oplqCross_reads_both`
computes both). So a single `Γ`-action realising both planes at once does not exist on a non-abelian
group without first inverting the plane variables of one of them.

DERIVED: no numeral. -/
theorem cross_word_both_handednesses (τ ν : Fin d) (x : Site d n)
    (U : Link d n → MassGap.SUN.SU N) :
    (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) (((τ, ν), x) : Plaq d n) U
          : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re
        = hsRe (((U (τ, x) * U (ν, shift τ x) * (U (τ, shift ν x))⁻¹ : MassGap.SUN.SU N))
              : Matrix (Fin N) (Fin N) ℂ)
            ((U (ν, x) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
      ∧ (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) (((τ, ν), x) : Plaq d n) U
          : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re
        = hsRe ((((U (τ, x))⁻¹ * U (ν, x) * U (τ, shift ν x) : MassGap.SUN.SU N))
              : Matrix (Fin N) (Fin N) ℂ)
            ((U (ν, shift τ x) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  refine ⟨hsRe_cross_word_left τ ν x U, ?_⟩
  rw [cross_word_left]
  exact re_trace_flip (U (τ, x)) (U (τ, shift ν x)) (U (ν, shift τ x)) (U (ν, x))

end HandednessLattice

section AuditF
#print axioms re_trace_inv
#print axioms trace_su_mul_comm
#print axioms re_trace_flip
#print axioms cross_word_both_handednesses
end AuditF


/-! ### Negative controls for Parts C and D -/

section CrossControls

/-- **NEGATIVE CONTROL — `SU(1)` cannot carry the obstruction.** Every element of `SU(1)` is the
`1 × 1` identity (its determinant is `1` and that is its only entry), so `Re tr` is `1` on the whole
group and no configuration makes any plaquette word negative.

So Part A's refutation is a fact about groups with room in them, not about the straddling geometry:
at `N = 1` the geometry is identical and the obstruction cannot fire.

DERIVED: `1` is the determinant of an `SU` element and the size of a `1 × 1` trace. -/
theorem negctl_su_one_trace (u : MassGap.SUN.SU 1) :
    (Matrix.trace ((u : Matrix (Fin 1) (Fin 1) ℂ))).re = 1 := by
  have hdet : Matrix.det (u : Matrix (Fin 1) (Fin 1) ℂ) = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp u.2).2
  rw [Matrix.det_fin_one] at hdet
  rw [Matrix.trace_fin_one, hdet]
  norm_num

/-- **NEGATIVE CONTROL, the consequence.** At `N = 1` every plaquette word of every configuration has
`Re tr = 1 > 0`, so `straddling_sum_not_paired_at_odd_lag`'s witness has no analogue there and the
sum-level obstruction is empty. The refutation is not a consequence of the reflection geometry alone.

DERIVED: `1` is the `SU(1)` trace; `0` is the sign a square has. -/
theorem negctl_su_one_no_witness {d n : ℕ} [NeZero n] (q : Plaq d n)
    (U : Link d n → MassGap.SUN.SU 1) :
    0 < (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) q U : MassGap.SUN.SU 1)
      : Matrix (Fin 1) (Fin 1) ℂ)).re := by
  rw [negctl_su_one_trace]
  norm_num

end CrossControls

section AuditCD
#print axioms hsReG_submatrix_equiv
#print axioms hsReG_blockDiagonal
#print axioms hsRe_dsum_conj
#print axioms hsRe_blockDiagonal_fin
#print axioms negctl_dsum_one_sided_not_invariant
#print axioms cross_word_left
#print axioms cross_word_right
#print axioms hsRe_cross_word_left
#print axioms hsRe_cross_word_right
#print axioms sum_hsRe_cross_word
#print axioms sum_hsRe_cross_word_gauge_invariant
#print axioms negctl_su_one_trace
#print axioms negctl_su_one_no_witness
end AuditCD


/-! ## The mirror-action identity at a link-reflection plane

`sum_oplaq_split` separates the action into four groups; it does not say the mirror group is the
positive group of the REFLECTED configuration. That exchange is what makes the Boltzmann weight a
paired product, and it is proved here — the odd-lag analogue of
`ActionSplit.sum_plqMinus_eq_plus_refl`.

The levels move differently from the even-lag case, and in two different ways at once. A plaquette
with a direction along the axis is carried by `reflSite τ (c − 1)`, so its base level `j` goes to
`n − j`; one with neither direction along the axis is carried by `reflSite τ c`, so its level goes to
`n − j + 1`. The one-step offset between the two families is the link reflection, and
`lv_refl_site_odd` is where it enters. -/

section Mirror

variable {d n : ℕ} [NeZero n]

/-- **The reflected level of a TRANSVERSE coordinate at a link reflection.** `c = a + a + 1`, so the
reflected coordinate is one step past the axis reflection's, and the level picks up the `+ 1` that
makes the two families of links sit on opposite sublattices. -/
theorem lv_refl_site_odd (a p : Fin n) :
    lv a ((a + a + 1) - p) = ((n - lv a p) % n + 1) % n := by
  have hstep : (a + a + 1 : Fin n) - p = ((a + a) - p) + 1 := by abel
  rw [hstep, lv_add_one, lv_refl_site]

variable (τ : Fin d) (a : Fin n) (m : ℕ)

/-- **The reflection carries the positive-half plaquettes onto the mirror ones.** -/
theorem oreflPlaq_plus_mem_minus (hm : n = 2 * m) (hm0 : 0 < m) {q : Plaq d n}
    (hq : q ∈ oplqPlus τ a m) : reflPlaq τ (a + a + 1) q ∈ oplqMinus τ a m := by
  have hn : 0 < n := NeZero.pos n
  obtain ⟨hdeg, h0, hle, hax⟩ := (mem_oplqPlus τ a m q).mp hq
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  have hdeg' : ¬ (μ = τ ∧ ν = τ) := hdeg
  have h0' : 0 < lv a (x τ) := h0
  have hle' : lv a (x τ) ≤ m := hle
  have hax' : (μ = τ ∨ ν = τ) → lv a (x τ) < m := hax
  have hjn : lv a (x τ) < n := lv_lt a (x τ)
  have hcancel : (a + a + 1 : Fin n) - 1 = a + a := by simp
  have hlevAx : lv a ((reflSite τ ((a + a + 1) - 1) x) τ) = n - lv a (x τ) := by
    rw [reflSite_axis, hcancel, lv_refl_site, Nat.mod_eq_of_lt (by omega)]
  have hinner : (n - lv a (x τ)) % n = n - lv a (x τ) := Nat.mod_eq_of_lt (by omega)
  have hlevTr : lv a ((reflSite τ (a + a + 1) x) τ) = (n - lv a (x τ) + 1) % n := by
    rw [reflSite_axis, lv_refl_site_odd, hinner]
  rw [mem_oplqMinus]
  by_cases hμ : μ = τ
  · have hν : ν ≠ τ := fun hc => hdeg' ⟨hμ, hc⟩
    have hlt := hax' (Or.inl hμ)
    rw [show reflPlaq τ (a + a + 1) (((μ, ν), x) : Plaq d n)
        = ((ν, τ), reflSite τ ((a + a + 1) - 1) x) by simp [reflPlaq, hμ]]
    refine ⟨fun h => hν h.1, ?_, fun _ => ?_⟩
    · show lv a ((reflSite τ ((a + a + 1) - 1) x) τ) = 0
          ∨ m < lv a ((reflSite τ ((a + a + 1) - 1) x) τ)
      rw [hlevAx]; exact Or.inr (by omega)
    · show m < lv a ((reflSite τ ((a + a + 1) - 1) x) τ)
      rw [hlevAx]; omega
  · by_cases hν : ν = τ
    · have hlt := hax' (Or.inr hν)
      rw [show reflPlaq τ (a + a + 1) (((μ, ν), x) : Plaq d n)
          = ((τ, μ), reflSite τ ((a + a + 1) - 1) x) by simp [reflPlaq, hμ, hν]]
      refine ⟨fun h => hμ h.2, ?_, fun _ => ?_⟩
      · show lv a ((reflSite τ ((a + a + 1) - 1) x) τ) = 0
            ∨ m < lv a ((reflSite τ ((a + a + 1) - 1) x) τ)
        rw [hlevAx]; exact Or.inr (by omega)
      · show m < lv a ((reflSite τ ((a + a + 1) - 1) x) τ)
        rw [hlevAx]; omega
    · rw [show reflPlaq τ (a + a + 1) (((μ, ν), x) : Plaq d n)
          = ((μ, ν), reflSite τ (a + a + 1) x) by simp [reflPlaq, hμ, hν]]
      refine ⟨hdeg', ?_, fun h => absurd h (fun hc => hc.elim hμ hν)⟩
      show lv a ((reflSite τ (a + a + 1) x) τ) = 0
          ∨ m < lv a ((reflSite τ (a + a + 1) x) τ)
      rw [hlevTr]
      rcases Nat.lt_or_ge (n - lv a (x τ) + 1) n with hlt | hge
      · exact Or.inr (by rw [Nat.mod_eq_of_lt hlt]; omega)
      · have he : n - lv a (x τ) + 1 = n := by omega
        exact Or.inl (by rw [he, Nat.mod_self])

/-- And back the other way, so the two groups are exchanged. -/
theorem oreflPlaq_minus_mem_plus (hm : n = 2 * m) (hm0 : 0 < m) {q : Plaq d n}
    (hq : q ∈ oplqMinus τ a m) : reflPlaq τ (a + a + 1) q ∈ oplqPlus τ a m := by
  have hn : 0 < n := NeZero.pos n
  obtain ⟨hdeg, hj, hax⟩ := (mem_oplqMinus τ a m q).mp hq
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  have hdeg' : ¬ (μ = τ ∧ ν = τ) := hdeg
  have hj' : lv a (x τ) = 0 ∨ m < lv a (x τ) := hj
  have hax' : (μ = τ ∨ ν = τ) → m < lv a (x τ) := hax
  have hjn : lv a (x τ) < n := lv_lt a (x τ)
  have hcancel : (a + a + 1 : Fin n) - 1 = a + a := by simp
  have hlevTr : lv a ((reflSite τ (a + a + 1) x) τ)
      = ((n - lv a (x τ)) % n + 1) % n := by
    rw [reflSite_axis, lv_refl_site_odd]
  rw [mem_oplqPlus]
  by_cases hμ : μ = τ
  · have hν : ν ≠ τ := fun hc => hdeg' ⟨hμ, hc⟩
    have hgt := hax' (Or.inl hμ)
    have hlevAx : lv a ((reflSite τ ((a + a + 1) - 1) x) τ) = n - lv a (x τ) := by
      rw [reflSite_axis, hcancel, lv_refl_site, Nat.mod_eq_of_lt (by omega)]
    rw [show reflPlaq τ (a + a + 1) (((μ, ν), x) : Plaq d n)
        = ((ν, τ), reflSite τ ((a + a + 1) - 1) x) by simp [reflPlaq, hμ]]
    refine ⟨fun h => hν h.1, ?_, ?_, fun _ => ?_⟩
    · show 0 < lv a ((reflSite τ ((a + a + 1) - 1) x) τ)
      rw [hlevAx]; omega
    · show lv a ((reflSite τ ((a + a + 1) - 1) x) τ) ≤ m
      rw [hlevAx]; omega
    · show lv a ((reflSite τ ((a + a + 1) - 1) x) τ) < m
      rw [hlevAx]; omega
  · by_cases hν : ν = τ
    · have hgt := hax' (Or.inr hν)
      have hlevAx : lv a ((reflSite τ ((a + a + 1) - 1) x) τ) = n - lv a (x τ) := by
        rw [reflSite_axis, hcancel, lv_refl_site, Nat.mod_eq_of_lt (by omega)]
      rw [show reflPlaq τ (a + a + 1) (((μ, ν), x) : Plaq d n)
          = ((τ, μ), reflSite τ ((a + a + 1) - 1) x) by simp [reflPlaq, hμ, hν]]
      refine ⟨fun h => hμ h.2, ?_, ?_, fun _ => ?_⟩
      · show 0 < lv a ((reflSite τ ((a + a + 1) - 1) x) τ)
        rw [hlevAx]; omega
      · show lv a ((reflSite τ ((a + a + 1) - 1) x) τ) ≤ m
        rw [hlevAx]; omega
      · show lv a ((reflSite τ ((a + a + 1) - 1) x) τ) < m
        rw [hlevAx]; omega
    · rw [show reflPlaq τ (a + a + 1) (((μ, ν), x) : Plaq d n)
          = ((μ, ν), reflSite τ (a + a + 1) x) by simp [reflPlaq, hμ, hν]]
      have hkey : 0 < lv a ((reflSite τ (a + a + 1) x) τ)
          ∧ lv a ((reflSite τ (a + a + 1) x) τ) ≤ m := by
        rcases hj' with h0 | hgt
        · have h1 : lv a ((reflSite τ (a + a + 1) x) τ) = 1 := by
            rw [hlevTr, h0, Nat.sub_zero, Nat.mod_self, Nat.zero_add]
            exact Nat.mod_eq_of_lt (by omega)
          rw [h1]; omega
        · have hin : (n - lv a (x τ)) % n = n - lv a (x τ) := Nat.mod_eq_of_lt (by omega)
          have hin2 : (n - lv a (x τ) + 1) % n = n - lv a (x τ) + 1 :=
            Nat.mod_eq_of_lt (by omega)
          have h1 : lv a ((reflSite τ (a + a + 1) x) τ) = n - lv a (x τ) + 1 := by
            rw [hlevTr, hin, hin2]
          rw [h1]; omega
      exact ⟨hdeg', hkey.1, hkey.2, fun h => absurd h (fun hc => hc.elim hμ hν)⟩

/-- **The straddling class is carried to itself.** The two fixed planes are exchanged or fixed by the
reflection but never mixed with the halves, so the four-way split of `sum_oplaq_split` is a
reflection-compatible partition and not merely a partition. -/
theorem oreflPlaq_cross_mem_cross (hm : n = 2 * m) (hm0 : 0 < m) {q : Plaq d n}
    (hq : q ∈ oplqCross τ a m) : reflPlaq τ (a + a + 1) q ∈ oplqCross τ a m := by
  have hn : 0 < n := NeZero.pos n
  obtain ⟨hdeg, hax, hlev⟩ := (mem_oplqCross τ a m q).mp hq
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  have hdeg' : ¬ (μ = τ ∧ ν = τ) := hdeg
  have hlev' : lv a (x τ) = 0 ∨ lv a (x τ) = m := hlev
  have hcancel : (a + a + 1 : Fin n) - 1 = a + a := by simp
  have hlevAx : lv a ((reflSite τ ((a + a + 1) - 1) x) τ) = (n - lv a (x τ)) % n := by
    rw [reflSite_axis, hcancel, lv_refl_site]
  rw [mem_oplqCross]
  have hgoal : lv a ((reflSite τ ((a + a + 1) - 1) x) τ) = 0
      ∨ lv a ((reflSite τ ((a + a + 1) - 1) x) τ) = m := by
    rw [hlevAx]
    rcases hlev' with h0 | hmm
    · left; rw [h0, Nat.sub_zero, Nat.mod_self]
    · right
      have hin : (n - m) % n = n - m := Nat.mod_eq_of_lt (by omega)
      rw [hmm, hin]
      omega
  rcases hax with hμ | hν
  · have hμ' : μ = τ := hμ
    have hν' : ν ≠ τ := fun hc => hdeg' ⟨hμ', hc⟩
    rw [show reflPlaq τ (a + a + 1) (((μ, ν), x) : Plaq d n)
        = ((ν, τ), reflSite τ ((a + a + 1) - 1) x) by simp [reflPlaq, hμ']]
    exact ⟨fun h => hν' h.1, Or.inr rfl, hgoal⟩
  · have hν' : ν = τ := hν
    have hμ' : μ ≠ τ := fun hc => hdeg' ⟨hc, hν'⟩
    rw [show reflPlaq τ (a + a + 1) (((μ, ν), x) : Plaq d n)
        = ((τ, μ), reflSite τ ((a + a + 1) - 1) x) by simp [reflPlaq, hμ', hν']]
    exact ⟨fun h => hμ' h.2, Or.inl rfl, hgoal⟩

/-- **THE MIRROR IDENTITY AT A LINK-REFLECTION PLANE.**

The mirror part of the action, evaluated at `U`, is the positive part evaluated at the REFLECTED
configuration. This is what makes the Boltzmann factor a paired product, and it is the exchange
`sum_oplaq_split` does not supply.

The holonomy of a reflected plaquette is only CONJUGATE to the image plaquette's
(`Reflect.hol_reflConf`); the Wilson density is a class function, which is why the identity holds on
the nose (`ActionSplit.density_reflConf`).

DERIVED: no numeral. -/
theorem sum_oplqMinus_eq_plus_refl {N : ℕ} (hm : n = 2 * m) (hm0 : 0 < m)
    (U : Link d n → MassGap.SUN.SU N) :
    ∑ q ∈ oplqMinus τ a m,
        MassGap.WilsonAction.wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)
      = ∑ q ∈ oplqPlus τ a m,
          MassGap.WilsonAction.wilsonDensity
            (wilsonHol (bd (d := d) (n := n)) q (reflConf τ (a + a + 1) U)) := by
  have himg : (oplqPlus (d := d) (n := n) τ a m).image (reflPlaq τ (a + a + 1))
      = oplqMinus τ a m := by
    ext q
    rw [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact oreflPlaq_plus_mem_minus τ a m hm hm0 hp
    · intro hq
      exact ⟨reflPlaq τ (a + a + 1) q, oreflPlaq_minus_mem_plus τ a m hm hm0 hq,
        reflPlaq_involutive τ (a + a + 1) q⟩
  have hinj : ∀ x ∈ oplqPlus (d := d) (n := n) τ a m,
      ∀ y ∈ oplqPlus (d := d) (n := n) τ a m,
      reflPlaq τ (a + a + 1) x = reflPlaq τ (a + a + 1) y → x = y :=
    fun x _ y _ h => (reflPlaq_involutive τ (a + a + 1)).injective h
  calc ∑ q ∈ oplqMinus τ a m,
        MassGap.WilsonAction.wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)
      = ∑ q ∈ (oplqPlus τ a m).image (reflPlaq τ (a + a + 1)),
          MassGap.WilsonAction.wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) := by
        rw [himg]
    _ = ∑ q ∈ oplqPlus τ a m,
          MassGap.WilsonAction.wilsonDensity
            (wilsonHol (bd (d := d) (n := n)) (reflPlaq τ (a + a + 1) q) U) :=
        Finset.sum_image hinj
    _ = ∑ q ∈ oplqPlus τ a m,
          MassGap.WilsonAction.wilsonDensity
            (wilsonHol (bd (d := d) (n := n)) q (reflConf τ (a + a + 1) U)) :=
        Finset.sum_congr rfl
          (fun q _ => (MassGap.ActionSplit.density_reflConf τ (a + a + 1) q U).symm)

end Mirror

/-! ### Negative control for the mirror identity -/

section MirrorControl

variable {d n : ℕ} [NeZero n]

/-- **NEGATIVE CONTROL — the mirror identity is not a relabelling that would hold for any set.**

The exchange `oplqPlus ↔ oplqMinus` is a fact about the two classes, not about `reflPlaq`. The
STRADDLING class is carried to itself (`oreflPlaq_cross_mem_cross`), so it is NOT exchanged with
anything, and the same image argument applied to it gives the class back rather than a mirror. Any
proof that "reflecting a class gives the complementary class" would therefore be wrong here.

DERIVED: no numeral. -/
theorem negctl_cross_not_exchanged (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) :
    (oplqCross (d := d) (n := n) τ a m).image (reflPlaq τ (a + a + 1))
      ⊆ oplqCross τ a m := by
  intro q hq
  rw [Finset.mem_image] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  exact oreflPlaq_cross_mem_cross τ a m hm hm0 hp

end MirrorControl

section AuditH
#print axioms lv_refl_site_odd
#print axioms oreflPlaq_plus_mem_minus
#print axioms oreflPlaq_minus_mem_plus
#print axioms oreflPlaq_cross_mem_cross
#print axioms sum_oplqMinus_eq_plus_refl
#print axioms negctl_cross_not_exchanged
end AuditH


/-! ## The handedness reconciliation — a SINGLE action for both fixed planes

`cross_word_both_handednesses` is the obstruction: the plane at level `0` presents the gauge as
`F ↦ g · F · h⁻¹` and the plane at level `m` presents it as `F ↦ g⁻¹ · F · h`, and the two compose in
opposite orders, so together they are not one action of the plane group.

They are reconciled, and the reconciliation is exactly the substitution
`CrossingIntegration.invLink` names: invert the plane variables on ONE of the two planes. The two
planes are disjoint sets of links, and both gauge links of a straddling plaquette lie in the SAME
plane (a transverse step does not move the axis coordinate), so one substitution on the plane
variables fixes every block at once.

* `planeAct` is the gauge action and `planeAct_mul` is the law `act h (act g x) = act (h * g) x` that
  `CrossingIntegration.wilson_crossing_pairing_nonneg` demands.
* `planeActOpp_mul` shows the other handedness composes as `g * h` — the opposite order, and on a
  non-abelian group a genuinely different law (`negctl_opposite_order_differs`,
  `negctl_su2_handedness_needs_substitution`).
* `mixedAct_invAt_eq_planeAct` is the reconciliation, and `mixedAct_invAt_mul` is the action law it
  buys.
* On the lattice, `invLink_measurePreserving` is the licence (product Haar is inversion-invariant,
  `Reflect.isInvInvariant_probHaar`), `oplqCross_gauge_same_plane` is the geometric fact that makes
  one substitution enough, and `cross_word_uniform` is both planes in one handedness.

ANSWER TO THE GATING QUESTION: the two handednesses ARE reconcilable. -/

section PlaneAction

variable {ι κ G : Type} [Group G]

/-- **The gauge action of the plane variables on the half.** Each block `l` reads two plane links
`A l` and `B l`, and they act on it as a gauge field acts on a link variable. -/
def planeAct (A B : ι → κ) (g : κ → G) (u : ι → G) : ι → G :=
  fun l => g (A l) * u l * (g (B l))⁻¹

@[simp] theorem planeAct_apply (A B : ι → κ) (g : κ → G) (u : ι → G) (l : ι) :
    planeAct A B g u l = g (A l) * u l * (g (B l))⁻¹ := rfl

theorem planeAct_one (A B : ι → κ) (u : ι → G) : planeAct A B (1 : κ → G) u = u := by
  funext l
  show (1 : κ → G) (A l) * u l * ((1 : κ → G) (B l))⁻¹ = u l
  simp [Pi.one_apply]

/-- **IT IS AN ACTION**, in the order `wilson_crossing_pairing_nonneg`'s `hmul` requires:
`act h (act g x) = act (h * g) x`. -/
theorem planeAct_mul (A B : ι → κ) (g h : κ → G) (u : ι → G) :
    planeAct A B h (planeAct A B g u) = planeAct A B (h * g) u := by
  funext l
  show h (A l) * (g (A l) * u l * (g (B l))⁻¹) * (h (B l))⁻¹
      = (h * g) (A l) * u l * ((h * g) (B l))⁻¹
  show h (A l) * (g (A l) * u l * (g (B l))⁻¹) * (h (B l))⁻¹
      = (h (A l) * g (A l)) * u l * (h (B l) * g (B l))⁻¹
  group

/-- **The OPPOSITE handedness**, which is what the second fixed plane presents. -/
def planeActOpp (A B : ι → κ) (g : κ → G) (u : ι → G) : ι → G :=
  fun l => (g (A l))⁻¹ * u l * g (B l)

@[simp] theorem planeActOpp_apply (A B : ι → κ) (g : κ → G) (u : ι → G) (l : ι) :
    planeActOpp A B g u l = (g (A l))⁻¹ * u l * g (B l) := rfl

/-- **AND IT COMPOSES IN THE OPPOSITE ORDER** — `g * h`, where `planeAct` gives `h * g`. On a
non-abelian group these are different laws, which is the whole obstruction. -/
theorem planeActOpp_mul (A B : ι → κ) (g h : κ → G) (u : ι → G) :
    planeActOpp A B h (planeActOpp A B g u) = planeActOpp A B (g * h) u := by
  funext l
  show (h (A l))⁻¹ * ((g (A l))⁻¹ * u l * g (B l)) * h (B l)
      = ((g * h) (A l))⁻¹ * u l * (g * h) (B l)
  show (h (A l))⁻¹ * ((g (A l))⁻¹ * u l * g (B l)) * h (B l)
      = (g (A l) * h (A l))⁻¹ * u l * (g (B l) * h (B l))
  group

/-- **THE ONE-LINE RECONCILIATION**: the opposite handedness is the SAME action at the inverted
plane variable. -/
theorem planeActOpp_eq_planeAct_inv (A B : ι → κ) (g : κ → G) (u : ι → G) :
    planeActOpp A B g u = planeAct A B g⁻¹ u := by
  funext l
  show (g (A l))⁻¹ * u l * g (B l) = g⁻¹ (A l) * u l * (g⁻¹ (B l))⁻¹
  simp [Pi.inv_apply]

/-- Invert the plane variables on a chosen set of plane links — `CrossingIntegration.invLink`, stated
over an arbitrary index so the algebra can be done once. -/
def invAt (P : κ → Prop) [DecidablePred P] (g : κ → G) : κ → G :=
  fun l => if P l then (g l)⁻¹ else g l

theorem invAt_invAt (P : κ → Prop) [DecidablePred P] (g : κ → G) : invAt P (invAt P g) = g := by
  funext l
  show (if P l then (if P l then (g l)⁻¹ else g l)⁻¹ else (if P l then (g l)⁻¹ else g l)) = g l
  by_cases h : P l
  · rw [if_pos h, if_pos h, inv_inv]
  · rw [if_neg h, if_neg h]

/-- **The action as the LATTICE presents it**: the blocks whose gauge links sit in the second plane
read the opposite handedness, the rest read the first. This is the mixed object
`cross_word_both_handednesses` exhibits, and on its own it is not an action. -/
def mixedAct (Q : ι → Prop) [DecidablePred Q] (A B : ι → κ) (g : κ → G) (u : ι → G) : ι → G :=
  fun l => if Q l then (g (A l))⁻¹ * u l * g (B l) else g (A l) * u l * (g (B l))⁻¹

/-- **THE HANDEDNESS RECONCILIATION.**

If each block's two gauge links lie in the second plane exactly when the block itself does — which on
the lattice is the statement that a transverse step does not move the axis coordinate
(`oplqCross_gauge_same_plane`) — then the mixed presentation is the UNIFORM action at the plane
variable with that plane inverted.

DERIVED: no numeral. -/
theorem mixedAct_eq_planeAct_invAt (Q : ι → Prop) [DecidablePred Q]
    (P : κ → Prop) [DecidablePred P] (A B : ι → κ)
    (hA : ∀ l, P (A l) ↔ Q l) (hB : ∀ l, P (B l) ↔ Q l) (g : κ → G) (u : ι → G) :
    mixedAct Q A B g u = planeAct A B (invAt P g) u := by
  funext l
  show (if Q l then (g (A l))⁻¹ * u l * g (B l) else g (A l) * u l * (g (B l))⁻¹)
      = (if P (A l) then (g (A l))⁻¹ else g (A l)) * u l
        * ((if P (B l) then (g (B l))⁻¹ else g (B l)))⁻¹
  by_cases h : Q l
  · rw [if_pos h, if_pos ((hA l).mpr h), if_pos ((hB l).mpr h), inv_inv]
  · rw [if_neg h, if_neg (fun hc => h ((hA l).mp hc)), if_neg (fun hc => h ((hB l).mp hc))]

/-- **The substituted variable is the one the crossing integration reads.** -/
theorem mixedAct_invAt_eq_planeAct (Q : ι → Prop) [DecidablePred Q]
    (P : κ → Prop) [DecidablePred P] (A B : ι → κ)
    (hA : ∀ l, P (A l) ↔ Q l) (hB : ∀ l, P (B l) ↔ Q l) (g : κ → G) (u : ι → G) :
    mixedAct Q A B (invAt P g) u = planeAct A B g u := by
  rw [mixedAct_eq_planeAct_invAt Q P A B hA hB, invAt_invAt]

/-- **AND IT THEN SATISFIES THE ACTION LAW** `act h (act g x) = act (h * g) x`, which is exactly
`wilson_crossing_pairing_nonneg`'s `hmul`. Item one, closed at the algebraic level. -/
theorem mixedAct_invAt_mul (Q : ι → Prop) [DecidablePred Q]
    (P : κ → Prop) [DecidablePred P] (A B : ι → κ)
    (hA : ∀ l, P (A l) ↔ Q l) (hB : ∀ l, P (B l) ↔ Q l) (g h : κ → G) (u : ι → G) :
    mixedAct Q A B (invAt P h) (mixedAct Q A B (invAt P g) u)
      = mixedAct Q A B (invAt P (h * g)) u := by
  rw [mixedAct_invAt_eq_planeAct Q P A B hA hB, mixedAct_invAt_eq_planeAct Q P A B hA hB,
    mixedAct_invAt_eq_planeAct Q P A B hA hB, planeAct_mul]

end PlaneAction

/-! ### Negative controls for the reconciliation -/

section HandednessControls

/-- **NEGATIVE CONTROL — the substitution is not cosmetic.** `planeAct` composes at `h * g` and
`planeActOpp` at `g * h`; on `Equiv.Perm (Fin 3)` those two conjugations genuinely differ, so no
single `Γ`-action realises both handednesses without the substitution.

DERIVED: `3` is the smallest order at which a symmetric group is non-abelian; the elements are
searched for, not chosen. -/
theorem negctl_opposite_order_differs :
    ∃ g h u : Equiv.Perm (Fin 3),
      (g * h)⁻¹ * u * (g * h) ≠ (h * g)⁻¹ * u * (h * g) := by decide

/-- **The two explicit `SU(2)` elements do not commute** — `diag(i, −i)` and `[[0,1],[−1,0]]`, both
already in the tree with their membership proofs. Their products differ in the `(0,1)` entry, `i`
against `−i`.

DERIVED: `0` and `1` index the entry that separates them; `i` and `−i` are computed. -/
theorem negctl_su2_noncomm :
    MassGap.SUN.h0 * MassGap.SUN.w
      ≠ MassGap.SUN.w * MassGap.SUN.h0 := by
  intro hc
  have h := congrArg (fun z : MassGap.SUN.SU 2 =>
      ((z : Matrix (Fin 2) (Fin 2) ℂ)) 0 1) hc
  simp only [Submonoid.coe_mul] at h
  have hI : (Complex.I : ℂ) = -Complex.I := by
    simpa [MassGap.SUN.h0, MassGap.SUN.w, MassGap.SUN.h0mat,
      MassGap.SUN.wmat, Matrix.mul_apply, Fin.sum_univ_two] using h
  exact Complex.I_ne_zero (by linear_combination hI / 2)

/-- **NEGATIVE CONTROL — the mixed presentation is NOT an action before the substitution, for the
ACTUAL gauge group.** With one block, two distinct plane links and the two `SU(2)` elements above,
`planeActOpp` composed twice is `(g·h)⁻¹` where the action law would give `(h·g)⁻¹`, and those differ
because the group does not commute. So `mixedAct_invAt_mul` is buying something.

DERIVED: the indices are a single block and two distinct plane links, the minimum the statement
needs; the group elements are the tree's own. -/
theorem negctl_su2_handedness_needs_substitution :
    ∃ (A B : Unit → Bool) (g h : Bool → MassGap.SUN.SU 2) (u : Unit → MassGap.SUN.SU 2),
      planeActOpp A B h (planeActOpp A B g u) ≠ planeActOpp A B (h * g) u := by
  refine ⟨fun _ => true, fun _ => false,
    fun b => if b then MassGap.SUN.h0 else 1,
    fun b => if b then MassGap.SUN.w else 1, fun _ => 1, ?_⟩
  intro hc
  have h := congrFun hc ()
  simp only [planeActOpp_apply, if_neg (Bool.false_ne_true), Pi.mul_apply] at h
  apply negctl_su2_noncomm
  have h3 := congrArg (fun z : MassGap.SUN.SU 2 => z⁻¹) h
  simpa using h3

end HandednessControls

/-! ### The reconciliation on the lattice -/

section HandednessLatticeFix

variable {d n N : ℕ} [NeZero n]

/-- **BOTH GAUGE LINKS OF A STRADDLING PLAQUETTE LIE IN THE SAME PLANE.** A transverse step does not
move the axis coordinate, so the two fixed axis links a straddling plaquette reads are at the same
level. This is what makes ONE substitution on the plane variables enough for every block at once —
the hypothesis `hA`/`hB` of `mixedAct_eq_planeAct_invAt`.

DERIVED: no numeral. -/
theorem oplqCross_gauge_same_plane {τ ν : Fin d} (hν : ν ≠ τ) (a : Fin n) (x : Site d n) :
    lv a (((τ, shift ν x) : Link d n).2 τ) = lv a (((τ, x) : Link d n).2 τ) :=
  lv_shift_of_ne hν a x

/-- **THE SUBSTITUTION IS MEASURE-PRESERVING.** Inverting the gauge variable on any set of links
preserves the product Haar measure, because Haar on a compact group is inversion-invariant
(`Reflect.isInvInvariant_probHaar`). This is the licence for the change of variables the
reconciliation needs; it is `ActionSplit.twist_measurePreserving` with the trivial relabelling.

DERIVED: no numeral. -/
theorem invLink_measurePreserving [DecidableEq (Link d n)] (R : Finset (Link d n)) :
    MeasurePreserving (invLink (d := d) (n := n) (G := MassGap.SUN.SU N) R)
      (cvol (Link d n) (probHaar (MassGap.SUN.SU N)))
      (cvol (Link d n) (probHaar (MassGap.SUN.SU N))) := by
  have hf : ∀ l : Link d n, MeasurePreserving
      (fun u : MassGap.SUN.SU N => if l ∈ R then u⁻¹ else u)
      (probHaar (MassGap.SUN.SU N)) (probHaar (MassGap.SUN.SU N)) := by
    intro l
    by_cases h : l ∈ R
    · simpa [h] using Measure.measurePreserving_inv (probHaar (MassGap.SUN.SU N))
    · have hid : (fun u : MassGap.SUN.SU N => if l ∈ R then u⁻¹ else u) = id := by
        funext u; simp [h]
      rw [hid]
      exact MeasurePreserving.id _
  have hmp := twist_measurePreserving (ι := Link d n) (μ := probHaar (MassGap.SUN.SU N))
    (1 : Equiv.Perm (Link d n)) (fun l u => if l ∈ R then u⁻¹ else u) hf
  have hfun : (twist (1 : Equiv.Perm (Link d n)) (fun l (u : MassGap.SUN.SU N) =>
      if l ∈ R then u⁻¹ else u))
      = (invLink (d := d) (n := n) (G := MassGap.SUN.SU N) R) := by
    funext U l
    show (if l ∈ R then (U ((1 : Equiv.Perm (Link d n)) l))⁻¹
        else U ((1 : Equiv.Perm (Link d n)) l))
      = (if l ∈ R then (U l)⁻¹ else U l)
    simp
  rwa [hfun] at hmp

/-- **THE STRADDLING WORD AT THE SECOND PLANE, IN THE FIRST PLANE'S HANDEDNESS.**

With the plane variables of this plane inverted, the word reads `hsRe (g̃_A · F · g̃_B⁻¹) F̄` — the same
shape as at the first plane, with `F` the link the positive half owns and `F̄` the mirror's. This is
`cross_word_both_handednesses`'s second reading with the substitution applied.

DERIVED: no numeral. -/
theorem cross_word_uniform_on_plane [DecidableEq (Link d n)] (τ ν : Fin d) (x : Site d n)
    (R : Finset (Link d n)) (hA : ((τ, x) : Link d n) ∈ R)
    (hB : ((τ, shift ν x) : Link d n) ∈ R) (U : Link d n → MassGap.SUN.SU N) :
    (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) (((τ, ν), x) : Plaq d n) U
        : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re
      = hsRe (((invLink R U (τ, x) * U (ν, x) * (invLink R U (τ, shift ν x))⁻¹
            : MassGap.SUN.SU N)) : Matrix (Fin N) (Fin N) ℂ)
          ((U (ν, shift τ x) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  have hiA : invLink R U ((τ, x) : Link d n) = (U (τ, x))⁻¹ := by
    show (if ((τ, x) : Link d n) ∈ R then (U (τ, x))⁻¹ else U (τ, x)) = (U (τ, x))⁻¹
    rw [if_pos hA]
  have hiB : invLink R U ((τ, shift ν x) : Link d n) = (U (τ, shift ν x))⁻¹ := by
    show (if ((τ, shift ν x) : Link d n) ∈ R then (U (τ, shift ν x))⁻¹ else U (τ, shift ν x))
      = (U (τ, shift ν x))⁻¹
    rw [if_pos hB]
  rw [hiA, hiB, inv_inv]
  exact (cross_word_both_handednesses τ ν x U).2

/-- **THE STRADDLING WORD AT THE FIRST PLANE IS UNTOUCHED BY THE SUBSTITUTION**, because that plane's
links are not in the substituted set. So after one substitution BOTH planes read
`hsRe (g̃_A · F · g̃_B⁻¹) F̄` — one handedness, one action, `planeAct_mul`.

DERIVED: no numeral. -/
theorem cross_word_uniform_off_plane [DecidableEq (Link d n)] (τ ν : Fin d) (x : Site d n)
    (R : Finset (Link d n)) (hA : ((τ, x) : Link d n) ∉ R)
    (hB : ((τ, shift ν x) : Link d n) ∉ R) (U : Link d n → MassGap.SUN.SU N) :
    (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) (((τ, ν), x) : Plaq d n) U
        : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re
      = hsRe (((invLink R U (τ, x) * U (ν, shift τ x) * (invLink R U (τ, shift ν x))⁻¹
            : MassGap.SUN.SU N)) : Matrix (Fin N) (Fin N) ℂ)
          ((U (ν, x) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  have hiA : invLink R U ((τ, x) : Link d n) = U (τ, x) := by
    show (if ((τ, x) : Link d n) ∈ R then (U (τ, x))⁻¹ else U (τ, x)) = U (τ, x)
    rw [if_neg hA]
  have hiB : invLink R U ((τ, shift ν x) : Link d n) = U (τ, shift ν x) := by
    show (if ((τ, shift ν x) : Link d n) ∈ R then (U (τ, shift ν x))⁻¹ else U (τ, shift ν x))
      = U (τ, shift ν x)
    rw [if_neg hB]
  rw [hiA, hiB]
  exact hsRe_cross_word_left τ ν x U

end HandednessLatticeFix

section AuditG
#print axioms planeAct_mul
#print axioms planeActOpp_mul
#print axioms planeActOpp_eq_planeAct_inv
#print axioms invAt_invAt
#print axioms mixedAct_eq_planeAct_invAt
#print axioms mixedAct_invAt_eq_planeAct
#print axioms mixedAct_invAt_mul
#print axioms negctl_opposite_order_differs
#print axioms negctl_su2_noncomm
#print axioms negctl_su2_handedness_needs_substitution
#print axioms oplqCross_gauge_same_plane
#print axioms invLink_measurePreserving
#print axioms cross_word_uniform_on_plane
#print axioms cross_word_uniform_off_plane
end AuditG


/-! ## THE ODD-LAG ACTION SPLIT, as a pointwise identity

Everything above assembles into one statement about the Boltzmann weight at a link-reflection plane:

    e^{−βS(U)}  =  h(U|S) · h(ΘU|S) · e^{−β·S_cross(U)}

with `h` a function of the positive half alone, the SAME `h` on both factors, and `S_cross` reading
only the straddling plaquettes. That is the analogue of `ActionSplit.integrand_eq_paired`, and it is
what the whole file is for.

* `actPlusO` reads `oblkS` alone (`actPlusO_local`) — sharper than the even-lag case, where the
  positive part also reads the shared block.
* `boltz_eq_paired_cross` is the factorisation, from `sum_oplaq_split` (the four classes),
  `sum_oplqDeg_zero` (the degenerate class is free) and `sum_oplqMinus_eq_plus_refl` (the mirror is
  the positive part of the reflected configuration).
* `actCross_eq_hsRe_uniform` turns the straddling factor into ONE cross form of two block-diagonal
  words, in one handedness, with the plane links absorbed as a gauge — the shape
  `CrossingIntegration.wilson_crossing_pairing_nonneg` reads.

What is NOT here is the integration: factoring the product Haar over `oblkS ⊔ oblkT ⊔ oblkR`,
transporting the mirror's variables to the positive half along the reflection, and applying the
crossing theorem. `WHAT REMAINS` below says exactly what that is. -/

section ActionSplitOdd

variable {d n : ℕ} [NeZero n] {N : ℕ}
variable (τ : Fin d) (a : Fin n) (m : ℕ)

/-- The positive half's part of the Wilson action at a link-reflection plane. -/
noncomputable def actPlusO (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  ∑ q ∈ oplqPlus τ a m,
    MassGap.WilsonAction.wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)

/-- The straddling part — the only place the fixed axis links appear. -/
noncomputable def actCrossO (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  ∑ q ∈ oplqCross τ a m,
    MassGap.WilsonAction.wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)

/-- **The positive part READS THE POSITIVE HALF ALONE.** At a link reflection it does not touch the
fixed set at all, which is where this differs from `ActionSplit.wPlane_local`. -/
theorem actPlusO_local (hm : n = 2 * m) (hm0 : 0 < m)
    (U V : Link d n → MassGap.SUN.SU N) (hS : ∀ l ∈ oblkS τ a m, U l = V l) :
    actPlusO (N := N) τ a m U = actPlusO τ a m V :=
  MassGap.ReflectionPositivity.action_on_congr_of_support (bd (d := d) (n := n))
    (MassGap.WilsonAction.wilsonDensity (N := N)) (oplqPlus τ a m) (oblkS τ a m)
    (fun p hp => oplaq_links_plus τ a m hm hm0 hp) U V hS

/-- **The straddling part reads everything**, which is the point: it is the only factor that couples
the two halves, and the coupling runs through the fixed axis links. -/
theorem actCrossO_local (hm : n = 2 * m) (hm0 : 0 < m)
    (U V : Link d n → MassGap.SUN.SU N)
    (hall : ∀ q ∈ oplqCross τ a m, ∀ l ∈ (bd q).map Prod.fst, U l = V l) :
    actCrossO (N := N) τ a m U = actCrossO τ a m V :=
  Finset.sum_congr rfl fun p hp => by
    rw [MassGap.ReflectionPositivity.hol_congr_on_support (bd (d := d) (n := n)) p U V
      (fun l hl => hall p hp l hl)]

/-- **THE ODD-LAG ACTION SPLIT.**

The Wilson action at a link-reflection plane is the positive half's part, plus the SAME function of
the reflected configuration, plus the straddling part. The degenerate class contributes nothing.

This is `ActionSplit.action_eq_split` and `sum_plqMinus_eq_plus_refl` in one, at the geometry that
file could not reach.

DERIVED: no numeral. -/
theorem action_eq_split_odd (hN : N ≠ 0) (hm : n = 2 * m) (hm0 : 0 < m)
    (U : Link d n → MassGap.SUN.SU N) :
    (MassGap.WilsonHypercubic.sysWilson N d n).action U
      = actPlusO τ a m U + actPlusO τ a m (reflConf τ (a + a + 1) U)
        + actCrossO τ a m U := by
  have hsplit := sum_oplaq_split (M := ℝ) τ a m
    (fun q => MassGap.WilsonAction.wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U))
  have hact : (MassGap.WilsonHypercubic.sysWilson N d n).action U
      = ∑ q : Plaq d n,
        MassGap.WilsonAction.wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) := rfl
  rw [hact, hsplit, sum_oplqDeg_zero τ hN U, sum_oplqMinus_eq_plus_refl τ a m hm hm0 U]
  show (0 + actCrossO τ a m U) + (actPlusO τ a m U + actPlusO τ a m (reflConf τ (a + a + 1) U))
      = actPlusO τ a m U + actPlusO τ a m (reflConf τ (a + a + 1) U) + actCrossO τ a m U
  ring

/-- **THE BOLTZMANN WEIGHT IS A PAIRED PRODUCT TIMES THE STRADDLING FACTOR.**

`e^{−βS} = h(U) · h(ΘU) · e^{−β S_cross}` with `h(U) = e^{−β·actPlusO U}`, the SAME `h` on both
factors, and `h` reading `oblkS` alone (`actPlusO_local`). Only the straddling factor couples the two
halves, and `actCross_eq_hsRe_uniform` says it does so through one gauge-invariant cross form.

DERIVED: no numeral. -/
theorem boltz_eq_paired_cross (hN : N ≠ 0) (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ)
    (U : Link d n → MassGap.SUN.SU N) :
    (MassGap.WilsonHypercubic.sysWilson N d n).boltz β U
      = (Real.exp (-β * actPlusO τ a m U)
          * Real.exp (-β * actPlusO τ a m (reflConf τ (a + a + 1) U)))
        * Real.exp (-β * actCrossO τ a m U) := by
  show Real.exp (-β * (MassGap.WilsonHypercubic.sysWilson N d n).action U) = _
  rw [action_eq_split_odd τ a m hN hm hm0 U, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- **The straddling factor, in the crossing engine's variables.**

`wilsonDensity W = 1 − (1/N)·Re tr W`, so the straddling part of the action is its own cardinality
minus `1/N` times the sum of the words' real traces — and that sum is one cross form
(`sum_hsRe_cross_word`). The sign is what makes `β ≥ 0` the right condition:
`e^{−β·S_cross} = e^{−β·card} · e^{(β/N)·(cross form)}`, and `β/N ≥ 0` is exactly
`wilson_crossing_pairing_nonneg`'s `hβ`.

DERIVED: `1` is the value of `wilsonDensity` at zero trace and the numerator of `1/N`; `N` is the
rank. Both come from `WilsonAction.wilsonDensity`, not from here. -/
theorem actCrossO_eq_trace_sum (hN : N ≠ 0) (U : Link d n → MassGap.SUN.SU N) :
    actCrossO (N := N) τ a m U
      = ((oplqCross τ a m).card : ℝ)
        - (1 / (N : ℝ)) * ∑ q ∈ oplqCross τ a m,
            (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) q U : MassGap.SUN.SU N)
              : Matrix (Fin N) (Fin N) ℂ)).re := by
  unfold actCrossO
  have hterm : ∀ q ∈ oplqCross τ a m,
      MassGap.WilsonAction.wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)
        = 1 - (1 / (N : ℝ))
          * (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) q U : MassGap.SUN.SU N)
              : Matrix (Fin N) (Fin N) ℂ)).re := fun q _ => rfl
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    mul_one, Finset.mul_sum]

end ActionSplitOdd

/-! ## HOW IT CLOSES

`boltz_eq_paired_cross` and `actCrossO_eq_trace_sum` put the integrand of
`CharacterExpansion.plaqReflPositive_of_pairing_nonneg` into the form
`CrossingIntegration.wilson_crossing_pairing_nonneg` consumes, POINTWISE. Parts E to K below turn
that pointwise identity into the inequality:

1. **The measure.** `integral_oblk_three_block` factors the product Haar over the three blocks — not
   as a product of integrals, which the straddling factor forbids, but as an ITERATED integral whose
   integrand couples all three. `integral_oblk_mirror` then transports the mirror's variables onto
   `oblkS`, so the two inner integrals run over the same block against the same measure.

2. **The family.** `oplqCross` indexes the blocks itself. Both orientations of every geometric
   plaquette appear and both contribute the same number (`re_tr_hol_swap`), so the direct sum simply
   carries each block twice; no bijection or fibre count is needed.

3. **One handedness.** Inverting the gauge on the UPPER plane alone — `invLink_measurePreserving`'s
   substitution, performed under the integral by `integral_odd_eq_oddIntegrand` — makes both planes
   read the same shape (`re_tr_hol_cross`).

4. **The action.** `planeARaw` and `planeBRaw` run the assignment backwards, from a half-link to the
   plane links of the plaquette that owns it, which is what makes the plane gauge a coordinatewise
   action on `oblkS → SU N` rather than a family indexed by blocks. This step and no other needs
   `2 ≤ m`: at extent two the level one step above the lower plane IS the upper plane, one half-link
   is owned by two plaquettes with different plane links, and no such assignment exists
   (`negctl_plane_assignment_collides_at_m_one`).

5. **The observable.** `aHalf` is `aObs` as a function of `oblkS` alone — `aObs_local` with
   `transverse_plaq_links_in_oblkS` — measurable and bounded, which is what `wilson_crossing_pairing_nonneg`'s
   `a` must be.

`odd_crossing_integral_nonneg` is the result, at `β' = β / N`, and `corrClay_reflection_positive`
composes it with Part H's plane choice. The `0 ≤ β` it carries is the sign of the coupling, not a
limitation of the method: `negctl_odd_discharge_needs_nonneg_coupling` shows the cross kernel is
nonnegative exactly there. -/

section AuditI
#print axioms actPlusO_local
#print axioms actCrossO_local
#print axioms action_eq_split_odd
#print axioms boltz_eq_paired_cross
#print axioms actCrossO_eq_trace_sum
end AuditI


/-! ## The composition — the axiom at even extent

`ReflectPositive.corrClay_rp_of` takes two inputs: `PlaqReflPositive` at EVERY lag, and strict
positivity at lag zero. The second is `PlaqVariance.corrClay_zero_pos`, which holds for every extent
and every coupling. Of the first, `ActionSplit.plaqReflPositive_of_even_lag` supplies the EVEN lags
whenever the extent is even.

So at even extent the whole of `Complete.wilson_reflection_positive_at` reduces to one hypothesis:
`PlaqReflPositive` at the ODD lags. `corrClay_rp_of_odd_lags` is that reduction.
`plaqReflPositive_odd_of_crossing` reduces that hypothesis in turn to a single integral,
`corrClay_rp_of_crossing` composes the two with the plane-choice glue of Part H, and
`odd_crossing_integral_nonneg` proves the integral nonnegative. `corrClay_reflection_positive` is the
composite, and it takes no hypothesis about the lattice at all.

`ActionSplit`'s `halfIntegral`, `pairing_eq_weighted_square` and `pairing_nonneg_of_local` are the
even-lag versions of the measure-theoretic step, and they assume the fixed block is NOT acted on —
which at a link reflection is false (`ActionSplit.reflConf_inverts_fixed_axis_link`). Parts E and F
replace them: the three-block factorisation does not require the plane to be inert, because the plane
variable is integrated LAST rather than conditioned on. -/

section Assembly

open MassGap.ReflectPositive

/-- **THE AXIOM AT EVEN EXTENT, REDUCED TO THE ODD LAGS ALONE.**

The conclusion is the conjunction `Complete.wilson_reflection_positive_at` asserts, at aperture `Nap`
— `Complete.wilsonCorrAt Nap β` is `WilsonBridge.corrClay (Nap + 1) β` by definition. The extent
`Nap + 1` is required EVEN, which is the case `ActionSplit.exists_even_extent_aperture` shows is
reachable without moving any pinned constant.

Two of the three inputs are discharged here and not assumed: the even lags by
`ActionSplit.plaqReflPositive_of_even_lag`, and lag-zero positivity by
`PlaqVariance.corrClay_zero_pos`. The odd lags remain a hypothesis.

DERIVED: `3` is the gauge group's rank, `4` the dimension, `(0, 1)` the plaquette's plane and `2` the
lag axis — all of them `WilsonBridge.corrClay`'s own choices, not this file's. -/
theorem corrClay_rp_of_odd_lags (Nap m : ℕ) (hm : Nap + 1 = 2 * m) (hm0 : 0 < m) (β : ℝ)
    (hodd : ∀ lag : Fin (Nap + 1), ¬ Even lag.val →
      PlaqReflPositive 3 (2 : Fin 4) lag β
        ((((0 : Fin 4), (1 : Fin 4)), (fun _ => 0 : Site 4 (Nap + 1))) : Plaq 4 (Nap + 1))) :
    (∀ lag, 0 ≤ MassGap.WilsonBridge.corrClay (Nap + 1) β lag)
      ∧ 0 < ∑ lag, MassGap.WilsonBridge.corrClay (Nap + 1) β lag := by
  classical
  refine corrClay_rp_of Nap β (fun lag => ?_) (MassGap.PlaqVariance.corrClay_zero_pos Nap β)
  by_cases h : Even lag.val
  · exact MassGap.ActionSplit.plaqReflPositive_of_even_lag (2 : Fin 4) m (by norm_num) hm hm0 h
      ((((0 : Fin 4), (1 : Fin 4)), (fun _ => 0 : Site 4 (Nap + 1))) : Plaq 4 (Nap + 1))
      (by
        intro hc
        have hzero : (0 : Fin 4) = 2 := hc.1
        exact absurd hzero (by decide)) β
  · exact hodd lag h

/-- **The remaining hypothesis, in integral form.** `CharacterExpansion.plaqReflPositive_of_pairing_nonneg`
divides out the partition function, so `PlaqReflPositive` at an odd lag is exactly nonnegativity of
the un-normalised pairing integral. Stating it this way names the object Parts B–D are about: the
integrand is `exp(−β·S)` with `S` split by `sum_oplaq_split`, and its straddling factor is the single
cross form `sum_hsRe_cross_word` exhibits. -/
theorem plaqReflPositive_of_integral {d n Nc : ℕ} [NeZero n] (hNc : Nc ≠ 0)
    (τ : Fin d) (cst : Fin n) (β : ℝ) (q₀ : Plaq d n)
    (hpair : ∀ aC : ℝ, 0 ≤ ∫ U,
      (MassGap.WilsonAction.wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) - aC)
        * (MassGap.WilsonAction.wilsonDensity
            (wilsonHol (bd (d := d) (n := n)) q₀ (reflConf τ cst U)) - aC)
        * (MassGap.WilsonHypercubic.sysWilson Nc d n).boltz β U
        ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU Nc)))) :
    PlaqReflPositive Nc τ cst β q₀ :=
  MassGap.CharacterExpansion.plaqReflPositive_of_pairing_nonneg hNc τ cst β q₀ hpair

end Assembly

section AuditE
#print axioms corrClay_rp_of_odd_lags
#print axioms plaqReflPositive_of_integral
end AuditE


/-! ## The odd-lag gap as ONE integral

`boltz_eq_paired_cross` regroups the integrand of
`CharacterExpansion.plaqReflPositive_of_pairing_nonneg` into the observable-times-weight of the
positive half, the SAME function of the reflected configuration, and the straddling factor. Doing
that regrouping under the integral sign reduces `PlaqReflPositive` at an odd lag to a single
statement — `plaqReflPositive_odd_of_crossing`'s hypothesis — which is exactly the object
`CrossingIntegration.wilson_crossing_pairing_nonneg` is about.

`aObs_local` is the half-locality that makes it that object: `aObs` reads `oblkS` alone, so under the
three-block factorisation it is a function of the positive half's variables and its partner is the
same function of the mirror's. -/

section OddGap

variable {d n : ℕ} [NeZero n] {N : ℕ}
variable (τ : Fin d) (a : Fin n) (m : ℕ)

/-- **The positive half's observable-and-weight**, the `a` of the crossing integration: the plaquette
energy centred at `aC`, times the positive half's Boltzmann factor. -/
noncomputable def aObs (q₀ : Plaq d n) (β aC : ℝ) (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  (MassGap.WilsonAction.wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) - aC)
    * Real.exp (-β * actPlusO τ a m U)

/-- **IT READS THE POSITIVE HALF ALONE**, provided the base plaquette does. Both factors do:
`actPlusO_local` for the weight, and the plaquette's own locality for the observable. This is what
makes it the crossing integration's `a : Ω → ℝ`.

DERIVED: no numeral. -/
theorem aObs_local (hm : n = 2 * m) (hm0 : 0 < m) (q₀ : Plaq d n)
    (hq₀ : ∀ l ∈ (bd q₀).map Prod.fst, l ∈ oblkS τ a m) (β aC : ℝ)
    (U V : Link d n → MassGap.SUN.SU N) (hS : ∀ l ∈ oblkS τ a m, U l = V l) :
    aObs (N := N) τ a m q₀ β aC U = aObs τ a m q₀ β aC V := by
  unfold aObs
  rw [MassGap.ReflectionPositivity.hol_congr_on_support (bd (d := d) (n := n)) q₀ U V
      (fun l hl => hS l (hq₀ l hl)),
    actPlusO_local τ a m hm hm0 U V hS]

/-- **THE ODD-LAG GAP, AS ONE INTEGRAL.**

`PlaqReflPositive` at a link-reflection plane follows from nonnegativity of the pairing of `aObs`
against its own reflection through the straddling factor — and nothing else. Every other ingredient
is discharged: the four-way action split, the mirror identity, the degenerate class, and the division
by the partition function.

This is the statement `CrossingIntegration.wilson_crossing_pairing_nonneg` proves in the abstract,
once the product measure is factored over `oblkS ⊔ oblkT ⊔ oblkR` and the mirror's variables are
transported to the positive half.

DERIVED: no numeral. -/
theorem plaqReflPositive_odd_of_crossing (hN : N ≠ 0) (hm : n = 2 * m) (hm0 : 0 < m)
    (β : ℝ) (q₀ : Plaq d n)
    (hcross : ∀ aC : ℝ, 0 ≤ ∫ U,
      aObs (N := N) τ a m q₀ β aC U
        * aObs τ a m q₀ β aC (reflConf τ (a + a + 1) U)
        * Real.exp (-β * actCrossO τ a m U)
        ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N)))) :
    MassGap.ReflectPositive.PlaqReflPositive N τ (a + a + 1) β q₀ := by
  refine plaqReflPositive_of_integral hN τ (a + a + 1) β q₀ (fun aC => ?_)
  have hint : ∀ U : Link d n → MassGap.SUN.SU N,
      (MassGap.WilsonAction.wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) - aC)
          * (MassGap.WilsonAction.wilsonDensity
              (wilsonHol (bd (d := d) (n := n)) q₀ (reflConf τ (a + a + 1) U)) - aC)
          * (MassGap.WilsonHypercubic.sysWilson N d n).boltz β U
        = aObs τ a m q₀ β aC U * aObs τ a m q₀ β aC (reflConf τ (a + a + 1) U)
          * Real.exp (-β * actCrossO τ a m U) := by
    intro U
    rw [boltz_eq_paired_cross τ a m hN hm hm0 β U]
    unfold aObs
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hint)]
  exact hcross aC

/-- **NEGATIVE CONTROL — the reduction keeps the centring constant.** `PlaqReflPositive` quantifies
over every centring `aC`, and `plaqReflPositive_odd_of_crossing`'s hypothesis does too: the constant
is not fixed anywhere in the reduction. A version that supplied one particular `aC` would prove
strictly less, and would not feed `ReflectPositive.corrHyper_nonneg_of_reflPositive`, which applies
the property at the mean.

DERIVED: no numeral; `aC` is the caller's. -/
theorem negctl_odd_gap_all_centrings (hN : N ≠ 0) (hm : n = 2 * m) (hm0 : 0 < m)
    (β : ℝ) (q₀ : Plaq d n)
    (hcross : ∀ aC : ℝ, 0 ≤ ∫ U,
      aObs (N := N) τ a m q₀ β aC U
        * aObs τ a m q₀ β aC (reflConf τ (a + a + 1) U)
        * Real.exp (-β * actCrossO τ a m U)
        ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N)))) (aC : ℝ) :
    0 ≤ MassGap.ReflectPositive.EW N β
      (fun U => (MassGap.ReflectPositive.plaqE N q₀ U - aC)
        * (MassGap.ReflectPositive.plaqE N q₀ (reflConf τ (a + a + 1) U) - aC)) :=
  plaqReflPositive_odd_of_crossing τ a m hN hm hm0 β q₀ hcross aC

end OddGap

section AuditJ
#print axioms aObs_local
#print axioms plaqReflPositive_odd_of_crossing
#print axioms negctl_odd_gap_all_centrings
end AuditJ


section AuditA
#print axioms sum_val_shift_parity
#print axioms cfgSum_inv
#print axioms reflConf_cfgSum
#print axioms reflLink_fixed_shift
#print axioms cfgSum_pair
#print axioms hol_cfgSum_left
#print axioms hol_cfgSum_right
#print axioms hol_cfgSum_oddCross
#print axioms sum_re_tr_cfgSum
#print axioms sum_re_tr_one
#print axioms straddling_sum_not_paired_at_odd_lag
#print axioms straddling_sum_not_matrix_paired_at_odd_lag
#print axioms no_half_function_for_straddling_sum
#print axioms exists_oddCross
#print axioms oddCross_four_dim
#print axioms negctl_paired_sum_is_nonneg
#print axioms negctl_sum_identity_positive
#print axioms negctl_parity_needs_even_extent
end AuditA

/-! ## Part E — the product measure over THREE blocks, as an iterated integral

`ActionSplit.block_factor` turns an integral over two DISJOINT blocks into a PRODUCT of two
integrals, and that is exactly what the straddling factor forbids here: it reads `oblkS`, `oblkT` and
`oblkR` at once, so no factor of the integrand is a function of one block alone
(`no_half_function_for_straddling_sum` is that statement). What is needed instead is a
REPARAMETRISATION — the same integral, written as an ITERATED integral over the three blocks'
variables, with the integrand still coupling all three.

Mathlib splits a product measure two ways: along a decidable predicate
(`measurePreserving_piEquivPiSubtypeProd`, whose second application lands on a subtype of a subtype)
or along a SUM index type (`measurePreserving_sumPiEquivProdPi`). The sum form is the one to use.
`blockEquiv3` presents the index type as `R ⊕ (S ⊕ T)`, so two applications of the sum split give the
three factors with no subtype of a subtype anywhere: each block appears as its own `Finset`
coercion, which is the type the rest of the file already speaks.

`join3` is the inverse reparametrisation — the configuration assembled from its three block
restrictions — and `integral_three_block` is the iterated-integral identity. Nothing here is specific
to the lattice; `integral_oblk_three_block` is the instance at the link-reflection blocks. -/

section ThreeBlock

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- **The index type, presented as the disjoint union of three blocks.**

The only inputs are pairwise disjointness and covering; nothing about what the blocks mean. The
coercion `↥R ⊕ (↥S ⊕ ↥T) ≃ ι` is what lets `measurePreserving_sumPiEquivProdPi` be applied twice, and
it is why the three factors come out as `↥R → Ω`, `↥S → Ω` and `↥T → Ω` rather than as nested
subtypes.

DERIVED: no numeral. -/
def blockEquiv3 (R S T : Finset ι) (hRS : Disjoint R S) (hRT : Disjoint R T)
    (hST : Disjoint S T) (hU : ∀ i : ι, i ∈ R ∨ i ∈ S ∨ i ∈ T) :
    (↥R ⊕ (↥S ⊕ ↥T)) ≃ ι where
  toFun := Sum.elim (fun j => (j : ι)) (Sum.elim (fun j => (j : ι)) (fun j => (j : ι)))
  invFun := fun i =>
    if h : i ∈ R then Sum.inl ⟨i, h⟩
    else if h2 : i ∈ S then Sum.inr (Sum.inl ⟨i, h2⟩)
    else Sum.inr (Sum.inr ⟨i, ((hU i).resolve_left h).resolve_left h2⟩)
  left_inv := by
    rintro (⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩)
    · simp [hi]
    · have hR : i ∉ R := fun hc => (Finset.disjoint_left.mp hRS) hc hi
      simp [hi, hR]
    · have hR : i ∉ R := fun hc => (Finset.disjoint_left.mp hRT) hc hi
      have hS : i ∉ S := fun hc => (Finset.disjoint_left.mp hST) hc hi
      simp [hR, hS]
  right_inv := by
    intro i
    by_cases h : i ∈ R
    · simp [h]
    · by_cases h2 : i ∈ S
      · simp [h, h2]
      · simp [h, h2]

/-- **The configuration assembled from its three block restrictions.** This is the change of
variables `integral_three_block` performs; `join3_mem_R`, `join3_mem_S` and `join3_mem_T` say it
reads each block's own variable and nothing else.

DERIVED: no numeral. -/
def join3 (R S T : Finset ι) (hRS : Disjoint R S) (hRT : Disjoint R T)
    (hST : Disjoint S T) (hU : ∀ i : ι, i ∈ R ∨ i ∈ S ∨ i ∈ T)
    (g : ↥R → Ω) (x : ↥S → Ω) (y : ↥T → Ω) : ι → Ω :=
  fun i => Sum.elim g (Sum.elim x y) ((blockEquiv3 R S T hRS hRT hST hU).symm i)

variable (R S T : Finset ι) (hRS : Disjoint R S) (hRT : Disjoint R T) (hST : Disjoint S T)
  (hU : ∀ i : ι, i ∈ R ∨ i ∈ S ∨ i ∈ T)

theorem join3_mem_R (g : ↥R → Ω) (x : ↥S → Ω) (y : ↥T → Ω) {i : ι} (hi : i ∈ R) :
    join3 R S T hRS hRT hST hU g x y i = g ⟨i, hi⟩ := by
  show Sum.elim g (Sum.elim x y)
      (if h : i ∈ R then Sum.inl ⟨i, h⟩
       else if h2 : i ∈ S then Sum.inr (Sum.inl ⟨i, h2⟩)
       else Sum.inr (Sum.inr ⟨i, _⟩)) = g ⟨i, hi⟩
  rw [dif_pos hi]
  rfl

theorem join3_mem_S (g : ↥R → Ω) (x : ↥S → Ω) (y : ↥T → Ω) {i : ι} (hi : i ∈ S) :
    join3 R S T hRS hRT hST hU g x y i = x ⟨i, hi⟩ := by
  have hR : i ∉ R := fun hc => (Finset.disjoint_left.mp hRS) hc hi
  show Sum.elim g (Sum.elim x y)
      (if h : i ∈ R then Sum.inl ⟨i, h⟩
       else if h2 : i ∈ S then Sum.inr (Sum.inl ⟨i, h2⟩)
       else Sum.inr (Sum.inr ⟨i, _⟩)) = x ⟨i, hi⟩
  rw [dif_neg hR, dif_pos hi]
  rfl

theorem join3_mem_T (g : ↥R → Ω) (x : ↥S → Ω) (y : ↥T → Ω) {i : ι} (hi : i ∈ T) :
    join3 R S T hRS hRT hST hU g x y i = y ⟨i, hi⟩ := by
  have hR : i ∉ R := fun hc => (Finset.disjoint_left.mp hRT) hc hi
  have hS : i ∉ S := fun hc => (Finset.disjoint_left.mp hST) hc hi
  show Sum.elim g (Sum.elim x y)
      (if h : i ∈ R then Sum.inl ⟨i, h⟩
       else if h2 : i ∈ S then Sum.inr (Sum.inl ⟨i, h2⟩)
       else Sum.inr (Sum.inr ⟨i, _⟩)) = y ⟨i, hi⟩
  rw [dif_neg hR, dif_neg hS]
  rfl

/-- **NEGATIVE CONTROL — the reparametrisation drops and duplicates nothing.** Joining a
configuration's own three restrictions returns that configuration. A partition that overlapped, or
that failed to cover, would fail exactly here, and the failure would be silent inside an integral:
the change of variables would still typecheck and would integrate the wrong function.

DERIVED: no numeral. -/
theorem join3_restrict (U : ι → Ω) :
    join3 R S T hRS hRT hST hU (fun j : ↥R => U (j : ι)) (fun j : ↥S => U (j : ι))
        (fun j : ↥T => U (j : ι)) = U := by
  funext i
  rcases hU i with hi | hi | hi
  · rw [join3_mem_R R S T hRS hRT hST hU _ _ _ hi]
  · rw [join3_mem_S R S T hRS hRT hST hU _ _ _ hi]
  · rw [join3_mem_T R S T hRS hRT hST hU _ _ _ hi]

/-- **THE PRODUCT HAAR MEASURE, FACTORED OVER THREE BLOCKS.**

The assembly map carries `(cvol R μ) ⊗ ((cvol S μ) ⊗ (cvol T μ))` to `cvol ι μ`. Two applications of
`measurePreserving_sumPiEquivProdPi` supply the two splits and `measurePreserving_piCongrLeft`
supplies the relabelling; the composite is `join3` on the nose.

DERIVED: no numeral. -/
theorem measurePreserving_join3 :
    MeasurePreserving
      (fun p : (↥R → Ω) × ((↥S → Ω) × (↥T → Ω)) =>
        join3 R S T hRS hRT hST hU p.1 p.2.1 p.2.2)
      ((cvol ↥R μ).prod ((cvol ↥S μ).prod (cvol ↥T μ))) (cvol ι μ) := by
  set e := blockEquiv3 R S T hRS hRT hST hU with he
  -- split the inner pair off the sum `↥S ⊕ ↥T`
  have hA : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : (↥S ⊕ ↥T) => Ω))
      (cvol (↥S ⊕ ↥T) μ) ((cvol ↥S μ).prod (cvol ↥T μ)) :=
    measurePreserving_sumPiEquivProdPi (fun _ : (↥S ⊕ ↥T) => μ)
  have hB : MeasurePreserving
      (Prod.map (id : (↥R → Ω) → (↥R → Ω))
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : (↥S ⊕ ↥T) => Ω)).symm)
      ((cvol ↥R μ).prod ((cvol ↥S μ).prod (cvol ↥T μ)))
      ((cvol ↥R μ).prod (cvol (↥S ⊕ ↥T) μ)) :=
    (MeasurePreserving.id _).prod (hA.symm _)
  -- split the outer pair off the sum `↥R ⊕ (↥S ⊕ ↥T)`
  have hC : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : (↥R ⊕ (↥S ⊕ ↥T)) => Ω)).symm
      ((cvol ↥R μ).prod (cvol (↥S ⊕ ↥T) μ)) (cvol (↥R ⊕ (↥S ⊕ ↥T)) μ) :=
    (measurePreserving_sumPiEquivProdPi (fun _ : (↥R ⊕ (↥S ⊕ ↥T)) => μ)).symm _
  -- and relabel the sum as the index type
  have hD : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : ι => Ω) e)
      (cvol (↥R ⊕ (↥S ⊕ ↥T)) μ) (cvol ι μ) := by
    simpa using measurePreserving_piCongrLeft (μ := fun _ : ι => μ) e
  have hcomp := hD.comp (hC.comp hB)
  -- the composite IS `join3`
  have hps : ∀ (W : ι → Ω) (k : ↥R ⊕ (↥S ⊕ ↥T)),
      (MeasurableEquiv.piCongrLeft (fun _ : ι => Ω) e).symm W k = W (e k) := fun _ _ => rfl
  have hkey : ∀ (g : ↥R → Ω) (x : ↥S → Ω) (y : ↥T → Ω),
      (MeasurableEquiv.piCongrLeft (fun _ : ι => Ω) e) (Sum.elim g (Sum.elim x y))
        = join3 R S T hRS hRT hST hU g x y := by
    intro g x y
    have hsym : (MeasurableEquiv.piCongrLeft (fun _ : ι => Ω) e).symm
        (join3 R S T hRS hRT hST hU g x y) = Sum.elim g (Sum.elim x y) := by
      funext k
      rw [hps]
      rcases k with ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩
      · exact join3_mem_R R S T hRS hRT hST hU g x y hi
      · exact join3_mem_S R S T hRS hRT hST hU g x y hi
      · exact join3_mem_T R S T hRS hRT hST hU g x y hi
    rw [← hsym]
    exact (MeasurableEquiv.piCongrLeft (fun _ : ι => Ω) e).apply_symm_apply _
  have hfun : ((MeasurableEquiv.piCongrLeft (fun _ : ι => Ω) e)
        ∘ ((MeasurableEquiv.sumPiEquivProdPi (fun _ : (↥R ⊕ (↥S ⊕ ↥T)) => Ω)).symm
          ∘ Prod.map (id : (↥R → Ω) → (↥R → Ω))
            (MeasurableEquiv.sumPiEquivProdPi (fun _ : (↥S ⊕ ↥T) => Ω)).symm))
      = fun p : (↥R → Ω) × ((↥S → Ω) × (↥T → Ω)) =>
          join3 R S T hRS hRT hST hU p.1 p.2.1 p.2.2 := by
    funext p
    obtain ⟨g, x, y⟩ := p
    exact hkey g x y
  rwa [hfun] at hcomp

/-- **THE ITERATED INTEGRAL OVER THE THREE BLOCKS.**

One integral over configurations, rewritten as three nested integrals over the blocks' own variables,
with the integrand free to couple all three — which is what distinguishes this from
`ActionSplit.block_factor`, where the integrand must factor and the answer is a product of numbers.

The only hypotheses are measurability and a bound, which a Boltzmann weight times a bounded
observable has; on a probability measure they give integrability
(`ActionSplit.integrable_of_bounded`).

DERIVED: no numeral. -/
theorem integral_three_block (F : (ι → Ω) → ℝ) (hFm : Measurable F) {C : ℝ}
    (hC : ∀ U, |F U| ≤ C) :
    (∫ U, F U ∂(cvol ι μ))
      = ∫ g, (∫ x, (∫ y, F (join3 R S T hRS hRT hST hU g x y) ∂(cvol ↥T μ))
          ∂(cvol ↥S μ)) ∂(cvol ↥R μ) := by
  have hmp := measurePreserving_join3 μ R S T hRS hRT hST hU
  have hjm : Measurable (fun p : (↥R → Ω) × ((↥S → Ω) × (↥T → Ω)) =>
      F (join3 R S T hRS hRT hST hU p.1 p.2.1 p.2.2)) := hFm.comp hmp.measurable
  rw [← integral_comp_of_mp hmp hFm,
    integral_prod _ (integrable_of_bounded _ hjm (fun z => hC _))]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun g => ?_))
  have hgm : Measurable (fun q : (↥S → Ω) × (↥T → Ω) =>
      F (join3 R S T hRS hRT hST hU g q.1 q.2)) := hjm.comp measurable_prodMk_left
  exact integral_prod _ (integrable_of_bounded _ hgm (fun z => hC _))

end ThreeBlock

/-! ### The three blocks of a link reflection, and the instances the plane group needs -/

section ThreeBlockLattice

variable {d n : ℕ} [NeZero n] {N : ℕ}
variable (τ : Fin d) (a : Fin n) (m : ℕ)

/-- **The three blocks cover the links** — `oblk_union_univ` read pointwise, which is the form
`blockEquiv3` takes. -/
theorem oblk_cover (l : Link d n) :
    l ∈ oblkR τ a m ∨ l ∈ oblkS τ a m ∨ l ∈ oblkT τ a m := by
  have h : l ∈ oblkS τ a m ∪ oblkT τ a m ∪ oblkR τ a m := by
    rw [oblk_union_univ]; exact Finset.mem_univ l
  rcases Finset.mem_union.mp h with h1 | h2
  · rcases Finset.mem_union.mp h1 with hS | hT
    · exact Or.inr (Or.inl hS)
    · exact Or.inr (Or.inr hT)
  · exact Or.inl h2

/-- The configuration assembled from its plane, positive-half and mirror variables. -/
noncomputable def joinO (g : ↥(oblkR τ a m) → MassGap.SUN.SU N)
    (x : ↥(oblkS τ a m) → MassGap.SUN.SU N) (y : ↥(oblkT τ a m) → MassGap.SUN.SU N) :
    Link d n → MassGap.SUN.SU N :=
  join3 (oblkR τ a m) (oblkS τ a m) (oblkT τ a m)
    (oblkS_disjoint_oblkR τ a m).symm (oblkT_disjoint_oblkR τ a m).symm
    (oblkS_disjoint_oblkT τ a m) (oblk_cover τ a m) g x y

/-- **THE PRODUCT HAAR OVER THE LINK-REFLECTION BLOCKS, AS AN ITERATED INTEGRAL.**

`integral_three_block` at the blocks of Part B: the plane `oblkR` outermost — which is where the
crossing integration needs it, since `wilson_crossing_pairing_nonneg` integrates the plane links
LAST — then the positive half, then the mirror.

DERIVED: no numeral. -/
theorem integral_oblk_three_block (F : (Link d n → MassGap.SUN.SU N) → ℝ) (hFm : Measurable F)
    {C : ℝ} (hC : ∀ U, |F U| ≤ C) :
    (∫ U, F U ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))))
      = ∫ g, (∫ x, (∫ y, F (joinO τ a m g x y)
            ∂(cvol ↥(oblkT τ a m) (probHaar (MassGap.SUN.SU N))))
          ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
        ∂(cvol ↥(oblkR τ a m) (probHaar (MassGap.SUN.SU N))) :=
  integral_three_block (probHaar (MassGap.SUN.SU N)) (oblkR τ a m) (oblkS τ a m) (oblkT τ a m)
    (oblkS_disjoint_oblkR τ a m).symm (oblkT_disjoint_oblkR τ a m).symm
    (oblkS_disjoint_oblkT τ a m) (oblk_cover τ a m) F hFm hC

end ThreeBlockLattice

section PlaneGroup

/-- **THE PLANE GROUP CARRIES WHAT THE CROSSING INTEGRATION ASKS OF IT.**

`wilson_crossing_pairing_nonneg` takes `Γ` a measurable group and `lam` a right-invariant probability
measure on it. With `Γ = oblkR → SU N` and `lam` the product Haar, all three are already available:
the product of measurable multiplications is measurable, the product of probability measures is one,
and the product of right-invariant measures is right-invariant — the last because
`CompactGauge.isMulRightInvariant_probHaar` supplies unimodularity coordinate by coordinate.

DERIVED: no numeral. -/
theorem plane_group_haar {κ : Type} [Fintype κ] (Nc : ℕ) :
    MeasurableMul (κ → MassGap.SUN.SU Nc)
      ∧ IsProbabilityMeasure (cvol κ (probHaar (MassGap.SUN.SU Nc)))
      ∧ (cvol κ (probHaar (MassGap.SUN.SU Nc))).IsMulRightInvariant :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end PlaneGroup

section ThreeBlockLattice2

variable {d n : ℕ} [NeZero n]
variable (τ : Fin d) (a : Fin n) (m : ℕ)


/-- **NEGATIVE CONTROL — the plane block is not empty, so the outer integral is not a formality.**
At even extent the fixed set contains the axis link at level `0` through the site `a`, so `Γ` is a
nontrivial group and `lam` is not a point mass. A reduction that quietly integrated over an empty
plane would prove nothing about the odd lag.

DERIVED: `0` is the lower plane's level, which is where the witness link sits. -/
theorem oblkR_nonempty : ((τ, Function.update (fun _ => a) τ a) : Link d n) ∈ oblkR τ a m := by
  rw [mem_oblkR]
  refine ⟨rfl, Or.inl ?_⟩
  show lv a ((Function.update (fun _ => a) τ a : Site d n) τ) = 0
  rw [Function.update_self]
  simp [lv]

end ThreeBlockLattice2

/-! ## Part F — the mirror's variables, transported to the positive half

After Part E the innermost integral runs over `oblkT → SU N`, and the crossing integration wants BOTH
inner integrals to run over the SAME half with the SAME measure. The transport is the reflection
itself: `reflLink` is a bijection `oblkT ≃ oblkS` (`oblkT_maps_oblkS` with `oblkS_maps_oblkT` as its
inverse) and `reflConf` daggers exactly the axis links among them, so the map is a RELABELLING
composed with a per-coordinate inversion — measure-preserving by the same two facts
`invLink_measurePreserving` uses, one of them for a different reason: here the relabelling is between
two DIFFERENT index types, which `ActionSplit.twist_measurePreserving` (a permutation of one index
set) does not cover. `measurePreserving_relabel_twist` is the two-type form.

`reflConf_joinO_mirror` is the payoff: with the mirror's variable written as `mirrorT y`, the
REFLECTED configuration restricted to the positive half is `y` itself. So the two factors of the
pairing become the same function of two independent `oblkS`-variables, which is the shape
`CrossingIntegration.wilson_crossing_pairing_nonneg` reads. -/

section Relabel

variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- **A relabelling BETWEEN TWO INDEX TYPES, twisted coordinatewise, preserves the product measure.**

`ActionSplit.twist_measurePreserving` is this with the two index types equal, which is what a
reflection of the whole link set is. The mirror transport is not a permutation of one index set: it
carries `oblkT` onto `oblkS`, two different `Finset` coercions, so the two-type form is what it
needs.

DERIVED: no numeral. -/
theorem measurePreserving_relabel_twist {κ κ' : Type} [Fintype κ] [Fintype κ']
    (e : κ ≃ κ') (σ : κ → Ω → Ω) (hσ : ∀ i, MeasurePreserving (σ i) μ μ) :
    MeasurePreserving (fun (V : κ' → Ω) (i : κ) => σ i (V (e i))) (cvol κ' μ) (cvol κ μ) := by
  have hrel : MeasurePreserving (fun (V : κ' → Ω) (i : κ) => V (e i)) (cvol κ' μ) (cvol κ μ) := by
    have h : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : κ' => Ω) e)
        (cvol κ μ) (cvol κ' μ) := by
      simpa using measurePreserving_piCongrLeft (μ := fun _ : κ' => μ) e
    exact h.symm _
  have hco : MeasurePreserving (fun (W : κ → Ω) (i : κ) => σ i (W i)) (cvol κ μ) (cvol κ μ) := by
    refine ⟨measurable_pi_lambda _ (fun i => (hσ i).measurable.comp (measurable_pi_apply i)), ?_⟩
    show Measure.map (fun (W : κ → Ω) (i : κ) => σ i (W i)) (cvol κ μ) = cvol κ μ
    rw [Measure.pi_map_pi (fun i => (hσ i).aemeasurable)]
    exact congrArg Measure.pi (funext fun i => (hσ i).map_eq)
  exact hco.comp hrel

end Relabel

section Mirror2

variable {d n : ℕ} [NeZero n] {N : ℕ}
variable (τ : Fin d) (a : Fin n) (m : ℕ)

/-- **The reflection carries the mirror onto the positive half** — the converse of
`oblkS_maps_oblkT`, and what makes `reflLink` a bijection between the two blocks. An axis level
`j > m` goes to `n − j`, strictly between `0` and `m`; a transverse level `0` goes to `1` and a
transverse level `j > m` to `n − j + 1`, which is at most `m` because `n − m = m`. -/
theorem oblkT_maps_oblkS (hm : n = 2 * m) (hm0 : 0 < m) {l : Link d n} (hl : l ∈ oblkT τ a m) :
    reflLink τ (a + a + 1) l ∈ oblkS τ a m := by
  have hn : 0 < n := NeZero.pos n
  have hjn : lv a (l.2 τ) < n := lv_lt a (l.2 τ)
  have hdir : (reflLink τ (a + a + 1) l).1 = l.1 := rfl
  have hcancel : (a + a + 1 : Fin n) - 1 = a + a := by simp
  rw [mem_oblkT] at hl
  rw [mem_oblkS, hdir]
  by_cases h : l.1 = τ
  · rw [if_pos h] at hl ⊢
    have hgt : m < lv a (l.2 τ) := hl
    have hinner : (n - lv a (l.2 τ)) % n = n - lv a (l.2 τ) := Nat.mod_eq_of_lt (by omega)
    have himg : (reflLink τ (a + a + 1) l).2 τ = (a + a) - l.2 τ := by
      rw [reflLink_coord_axis _ h, hcancel]
    rw [himg, lv_refl_site, hinner]
    omega
  · rw [if_neg h] at hl ⊢
    have himg : (reflLink τ (a + a + 1) l).2 τ = ((a + a) - l.2 τ) + 1 := by
      rw [reflLink_coord_transverse _ h]
      abel
    rw [himg, lv_add_one, lv_refl_site]
    rcases hl with h0 | hgt
    · have hs : ((n - lv a (l.2 τ)) % n + 1) % n = 1 := by
        rw [h0, Nat.sub_zero, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      rw [hs]; omega
    · have hinner : (n - lv a (l.2 τ)) % n = n - lv a (l.2 τ) := Nat.mod_eq_of_lt (by omega)
      have hs : ((n - lv a (l.2 τ)) % n + 1) % n = n - lv a (l.2 τ) + 1 := by
        rw [hinner, Nat.mod_eq_of_lt (by omega)]
      rw [hs]; omega

/-- **The reflection as a BIJECTION of the two halves.** Its inverse is itself
(`reflLink_involutive`); the two membership lemmas are what make it typecheck in both directions.

DERIVED: `2` and `0` are the extent hypotheses `n = 2m` and `0 < m` — the geometry of an even extent
with a nonempty half, not a choice; `1` is the link reflection's one-step offset in the reflection
constant `a + a + 1`, which is what makes `2x = c` unsolvable and `2x = c − 1` solvable. -/
def mirrorEquivTS (hm : n = 2 * m) (hm0 : 0 < m) :
    ↥(oblkT τ a m) ≃ ↥(oblkS τ a m) where
  toFun := fun l => ⟨reflLink τ (a + a + 1) (l : Link d n), oblkT_maps_oblkS τ a m hm hm0 l.2⟩
  invFun := fun l => ⟨reflLink τ (a + a + 1) (l : Link d n), oblkS_maps_oblkT τ a m hm hm0 l.2⟩
  left_inv := fun l => Subtype.ext (reflLink_involutive τ (a + a + 1) (l : Link d n))
  right_inv := fun l => Subtype.ext (reflLink_involutive τ (a + a + 1) (l : Link d n))

/-- **The mirror's variable, written as a variable of the positive half.** The relabelling is
`mirrorEquivTS` and the twist is the dagger the reflection puts on axis links — the same `σ`
`Reflect.reflConf` carries, restricted to the mirror block.

DERIVED: `2` and `0` are the extent hypotheses `n = 2m` and `0 < m`; `1` is the link reflection's
one-step offset in `a + a + 1`. All three are the geometry, not choices. -/
noncomputable def mirrorT (hm : n = 2 * m) (hm0 : 0 < m)
    (y : ↥(oblkS τ a m) → MassGap.SUN.SU N) : ↥(oblkT τ a m) → MassGap.SUN.SU N :=
  fun l => if (l : Link d n).1 = τ then (y (mirrorEquivTS τ a m hm hm0 l))⁻¹
    else y (mirrorEquivTS τ a m hm hm0 l)

/-- **THE TRANSPORT IS MEASURE-PRESERVING.** Relabelling by a bijection of index sets and inverting
on some coordinates; Haar is inversion-invariant (`Reflect.isInvInvariant_probHaar`), so every
coordinate map preserves the factor.

DERIVED: no numeral. -/
theorem measurePreserving_mirrorT (hm : n = 2 * m) (hm0 : 0 < m) :
    MeasurePreserving (mirrorT (N := N) τ a m hm hm0)
      (cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N)))
      (cvol ↥(oblkT τ a m) (probHaar (MassGap.SUN.SU N))) := by
  have hσ : ∀ l : ↥(oblkT τ a m), MeasurePreserving
      (fun u : MassGap.SUN.SU N => if (l : Link d n).1 = τ then u⁻¹ else u)
      (probHaar (MassGap.SUN.SU N)) (probHaar (MassGap.SUN.SU N)) := by
    intro l
    by_cases h : (l : Link d n).1 = τ
    · simpa [h] using Measure.measurePreserving_inv (probHaar (MassGap.SUN.SU N))
    · have hid : (fun u : MassGap.SUN.SU N => if (l : Link d n).1 = τ then u⁻¹ else u) = id := by
        funext u; simp [h]
      rw [hid]
      exact MeasurePreserving.id _
  exact measurePreserving_relabel_twist (probHaar (MassGap.SUN.SU N))
    (mirrorEquivTS τ a m hm hm0)
    (fun l u => if (l : Link d n).1 = τ then u⁻¹ else u) hσ

/-- **THE REFLECTED CONFIGURATION, RESTRICTED TO THE POSITIVE HALF, IS THE TRANSPORTED VARIABLE.**

With the mirror's block filled by `mirrorT y`, the reflection of the assembled configuration reads
`y` on `oblkS` — the dagger applied twice on an axis link is the identity, and on a transverse link
there is no dagger at all. This is what makes the pairing two evaluations of ONE function of the
half, at two independent variables.

DERIVED: no numeral. -/
theorem reflConf_joinO_mirror (hm : n = 2 * m) (hm0 : 0 < m)
    (g : ↥(oblkR τ a m) → MassGap.SUN.SU N) (x y : ↥(oblkS τ a m) → MassGap.SUN.SU N)
    {l : Link d n} (hl : l ∈ oblkS τ a m) :
    reflConf τ (a + a + 1) (joinO τ a m g x (mirrorT τ a m hm hm0 y)) l = y ⟨l, hl⟩ := by
  have hT : reflLink τ (a + a + 1) l ∈ oblkT τ a m := oblkS_maps_oblkT τ a m hm hm0 hl
  have hdir : (reflLink τ (a + a + 1) l).1 = l.1 := rfl
  have hinv : (mirrorEquivTS τ a m hm hm0) ⟨reflLink τ (a + a + 1) l, hT⟩ = ⟨l, hl⟩ :=
    Subtype.ext (reflLink_involutive τ (a + a + 1) l)
  have hjoin : joinO τ a m g x (mirrorT τ a m hm hm0 y) (reflLink τ (a + a + 1) l)
      = mirrorT τ a m hm hm0 y ⟨reflLink τ (a + a + 1) l, hT⟩ :=
    join3_mem_T (oblkR τ a m) (oblkS τ a m) (oblkT τ a m)
      (oblkS_disjoint_oblkR τ a m).symm (oblkT_disjoint_oblkR τ a m).symm
      (oblkS_disjoint_oblkT τ a m) (oblk_cover τ a m) g x _ hT
  have hmir : mirrorT τ a m hm hm0 y ⟨reflLink τ (a + a + 1) l, hT⟩
      = if l.1 = τ then (y ⟨l, hl⟩)⁻¹ else y ⟨l, hl⟩ := by
    show (if (reflLink τ (a + a + 1) l).1 = τ
        then (y ((mirrorEquivTS τ a m hm hm0) ⟨reflLink τ (a + a + 1) l, hT⟩))⁻¹
        else y ((mirrorEquivTS τ a m hm hm0) ⟨reflLink τ (a + a + 1) l, hT⟩))
      = if l.1 = τ then (y ⟨l, hl⟩)⁻¹ else y ⟨l, hl⟩
    rw [hdir, hinv]
  show (if l.1 = τ
      then (joinO τ a m g x (mirrorT τ a m hm hm0 y) (reflLink τ (a + a + 1) l))⁻¹
      else joinO τ a m g x (mirrorT τ a m hm hm0 y) (reflLink τ (a + a + 1) l)) = y ⟨l, hl⟩
  rw [hjoin, hmir]
  by_cases h : l.1 = τ
  · rw [if_pos h, if_pos h, inv_inv]
  · rw [if_neg h, if_neg h]

/-- **NEGATIVE CONTROL — the transport is not the identity relabelling.** On an AXIS link of the
mirror the transported variable is the INVERSE of the half's, and that dagger is the whole difference
between a link reflection and a site reflection: `ActionSplit`'s even-lag weld assumes the shared
block is NOT acted on, and here it is. A transport that dropped the inversion would be the map that
case uses, and it would be the wrong map.

DERIVED: no numeral. -/
theorem negctl_mirrorT_daggers_axis (hm : n = 2 * m) (hm0 : 0 < m)
    (y : ↥(oblkS τ a m) → MassGap.SUN.SU N) (l : ↥(oblkT τ a m)) (hax : (l : Link d n).1 = τ) :
    mirrorT τ a m hm hm0 y l = (y (mirrorEquivTS τ a m hm hm0 l))⁻¹ := by
  show (if (l : Link d n).1 = τ then (y (mirrorEquivTS τ a m hm hm0 l))⁻¹
      else y (mirrorEquivTS τ a m hm hm0 l)) = _
  rw [if_pos hax]

end Mirror2

/-! ### The iterated integral with both halves on the SAME block -/

section MirrorIntegral

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Ω : Type} [MeasurableSpace Ω]

/-- The assembly map is measurable in all three block variables at once. -/
theorem measurable_join3 (R S T : Finset ι) (hRS : Disjoint R S) (hRT : Disjoint R T)
    (hST : Disjoint S T) (hU : ∀ i : ι, i ∈ R ∨ i ∈ S ∨ i ∈ T) :
    Measurable (fun p : (↥R → Ω) × ((↥S → Ω) × (↥T → Ω)) =>
      join3 R S T hRS hRT hST hU p.1 p.2.1 p.2.2) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  rcases hU i with hi | hi | hi
  · have h : (fun p : (↥R → Ω) × ((↥S → Ω) × (↥T → Ω)) =>
        join3 R S T hRS hRT hST hU p.1 p.2.1 p.2.2 i) = fun p => p.1 ⟨i, hi⟩ :=
      funext (fun p => join3_mem_R R S T hRS hRT hST hU p.1 p.2.1 p.2.2 hi)
    rw [h]
    exact (measurable_pi_apply _).comp measurable_fst
  · have h : (fun p : (↥R → Ω) × ((↥S → Ω) × (↥T → Ω)) =>
        join3 R S T hRS hRT hST hU p.1 p.2.1 p.2.2 i) = fun p => p.2.1 ⟨i, hi⟩ :=
      funext (fun p => join3_mem_S R S T hRS hRT hST hU p.1 p.2.1 p.2.2 hi)
    rw [h]
    exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
  · have h : (fun p : (↥R → Ω) × ((↥S → Ω) × (↥T → Ω)) =>
        join3 R S T hRS hRT hST hU p.1 p.2.1 p.2.2 i) = fun p => p.2.2 ⟨i, hi⟩ :=
      funext (fun p => join3_mem_T R S T hRS hRT hST hU p.1 p.2.1 p.2.2 hi)
    rw [h]
    exact (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)

end MirrorIntegral

section MirrorIntegralLattice

variable {d n : ℕ} [NeZero n] {N : ℕ}
variable (τ : Fin d) (a : Fin n) (m : ℕ)

theorem measurable_joinO_right (g : ↥(oblkR τ a m) → MassGap.SUN.SU N)
    (x : ↥(oblkS τ a m) → MassGap.SUN.SU N) :
    Measurable (fun y : ↥(oblkT τ a m) → MassGap.SUN.SU N => joinO τ a m g x y) :=
  (measurable_join3 (oblkR τ a m) (oblkS τ a m) (oblkT τ a m)
      (oblkS_disjoint_oblkR τ a m).symm (oblkT_disjoint_oblkR τ a m).symm
      (oblkS_disjoint_oblkT τ a m) (oblk_cover τ a m)).comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))

/-- **THE ITERATED INTEGRAL, WITH BOTH HALVES ON `oblkS`.**

Part E's three blocks with the mirror's variable transported: the plane outermost, then TWO
independent copies of the positive half's variable against the SAME measure. That is exactly the
`∫ lam ∫ nu ∫ nu` of `CrossingIntegration.wilson_crossing_pairing_nonneg`, and it is the last change
of variables that inequality needs before the integrand identification.

DERIVED: no numeral. -/
theorem integral_oblk_mirror (hm : n = 2 * m) (hm0 : 0 < m)
    (F : (Link d n → MassGap.SUN.SU N) → ℝ) (hFm : Measurable F) {C : ℝ}
    (hC : ∀ U, |F U| ≤ C) :
    (∫ U, F U ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))))
      = ∫ g, (∫ x, (∫ y, F (joinO τ a m g x (mirrorT τ a m hm hm0 y))
            ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
          ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
        ∂(cvol ↥(oblkR τ a m) (probHaar (MassGap.SUN.SU N))) := by
  rw [integral_oblk_three_block τ a m F hFm hC]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun g => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  exact (integral_comp_of_mp (measurePreserving_mirrorT τ a m hm hm0)
    (hFm.comp (measurable_joinO_right τ a m g x))).symm

end MirrorIntegralLattice

/-! ## Part G — the instances the crossing integration asks for

`plane_group_haar` already supplies `Γ`'s three. The remaining two are the action on the half and the
word's coordinate bound, and both are settled here in the form the theorem takes:

* `planeAct_measurePreserving` — the plane gauge acts on the half measure-preservingly, coordinate by
  coordinate, by bi-invariance of Haar (`CompactGauge.isMulRightInvariant_probHaar` is the right half
  of it); `measurable_uncurry_planeAct` is the joint measurability `hactm` asks for, and
  `planeAct_mul` above is `hmul`.
* `abs_coord_le_one_of_entries` with `entry_blockDiagonal_fin_norm_le_one` — every coordinate of the
  block-diagonal word is either a unitary entry (`SUN.unitary_entry_norm_le_one`) or `0`. -/

section GaugeActionMeasure

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- **THE PLANE GAUGE ACTION PRESERVES THE HALF'S PRODUCT HAAR.** Each coordinate is
`u ↦ g_A · u · g_B⁻¹`, a left translation composed with a right translation, and probability Haar on
a compact group is invariant under both (`CompactGauge.isMulRightInvariant_probHaar` for the second).

DERIVED: no numeral. -/
theorem planeAct_measurePreserving (A B : ι → κ) (g : κ → MassGap.SUN.SU N) :
    MeasurePreserving (planeAct A B g)
      (cvol ι (probHaar (MassGap.SUN.SU N))) (cvol ι (probHaar (MassGap.SUN.SU N))) := by
  have hσ : ∀ i : ι, MeasurePreserving
      (fun u : MassGap.SUN.SU N => g (A i) * u * (g (B i))⁻¹)
      (probHaar (MassGap.SUN.SU N)) (probHaar (MassGap.SUN.SU N)) := by
    intro i
    have h := (measurePreserving_mul_left (probHaar (MassGap.SUN.SU N)) (g (A i))).comp
      (measurePreserving_mul_right (probHaar (MassGap.SUN.SU N)) (g (B i))⁻¹)
    convert h using 1
    funext u
    simp [Function.comp, mul_assoc]
  have hmp := twist_measurePreserving (ι := ι) (probHaar (MassGap.SUN.SU N))
    (1 : Equiv.Perm ι) (fun i u => g (A i) * u * (g (B i))⁻¹) hσ
  have hfun : twist (1 : Equiv.Perm ι)
      (fun i (u : MassGap.SUN.SU N) => g (A i) * u * (g (B i))⁻¹) = planeAct A B g := by
    funext u i
    show g (A ((1 : Equiv.Perm ι) i)) * u ((1 : Equiv.Perm ι) i)
        * (g (B ((1 : Equiv.Perm ι) i)))⁻¹ = g (A i) * u i * (g (B i))⁻¹
    simp
  rwa [hfun] at hmp

end GaugeActionMeasure

section GaugeActionMeasurable

variable {ι κ : Type} {N : ℕ}

/-- **THE ACTION IS JOINTLY MEASURABLE** — `hactm`. Multiplication and inversion are measurable on
`SU(N)` (`SUN` supplies `MeasurableMul₂` and `MeasurableInv`), and the action reads three
coordinates.

DERIVED: no numeral. -/
theorem measurable_uncurry_planeAct (A B : ι → κ) :
    Measurable (Function.uncurry
      (fun (g : κ → MassGap.SUN.SU N) (u : ι → MassGap.SUN.SU N) => planeAct A B g u)) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  show Measurable (fun p : (κ → MassGap.SUN.SU N) × (ι → MassGap.SUN.SU N) =>
    p.1 (A i) * p.2 i * (p.1 (B i))⁻¹)
  exact (((measurable_pi_apply (A i)).comp measurable_fst).mul
      ((measurable_pi_apply i).comp measurable_snd)).mul
    (((measurable_pi_apply (B i)).comp measurable_fst).inv)

end GaugeActionMeasurable

section WordBound

/-- **A matrix whose entries have norm at most one has every real coordinate bounded by one** — the
form `wilson_crossing_pairing_nonneg`'s `hXb` takes. A coordinate is a real or imaginary part, and
both are bounded by the modulus.

DERIVED: `1` is the bound a unitary entry carries (`SUN.unitary_entry_norm_le_one`), not a chosen
cut. -/
theorem abs_coord_le_one_of_entries {Nc : ℕ} {A : Matrix (Fin Nc) (Fin Nc) ℂ}
    (h : ∀ i j, ‖A i j‖ ≤ 1) (p : Coord Nc) : |coord p A| ≤ 1 := by
  unfold coord
  split
  · exact (Complex.abs_re_le_norm _).trans (h _ _)
  · exact (Complex.abs_im_le_norm _).trans (h _ _)

/-- **Every entry of a block-diagonal of `SU(N)` matrices, relabelled to a `Fin`, has norm at most
one** — it is a unitary entry on the diagonal blocks and `0` off them.

DERIVED: `1` is the unitary entry bound; `0` is the off-block entry. -/
theorem entry_blockDiagonal_fin_norm_le_one {K : Type} [Fintype K] [DecidableEq K] {N : ℕ}
    (W : K → MassGap.SUN.SU N) (p q : Fin (Fintype.card (Fin N × K))) :
    ‖((Matrix.blockDiagonal (fun k => ((W k : MassGap.SUN.SU N)
        : Matrix (Fin N) (Fin N) ℂ))).submatrix
        (Fintype.equivFin (Fin N × K)).symm (Fintype.equivFin (Fin N × K)).symm) p q‖ ≤ 1 := by
  show ‖Matrix.blockDiagonal (fun k => ((W k : MassGap.SUN.SU N)
      : Matrix (Fin N) (Fin N) ℂ))
        ((Fintype.equivFin (Fin N × K)).symm p) ((Fintype.equivFin (Fin N × K)).symm q)‖ ≤ 1
  rw [Matrix.blockDiagonal_apply]
  set k := ((Fintype.equivFin (Fin N × K)).symm p).2 with hkdef
  by_cases hk : k = ((Fintype.equivFin (Fin N × K)).symm q).2
  · rw [if_pos hk]
    have hu : ((W k : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
        ∈ Matrix.unitaryGroup (Fin N) ℂ :=
      (Matrix.mem_specialUnitaryGroup_iff.mp (W k).2).1
    exact MassGap.SUN.unitary_entry_norm_le_one N hu _ _
  · rw [if_neg hk]
    simp

end WordBound

/-! ## Part H — the glue: which plane an odd lag gets, and where it puts the base plaquette

`corrClay_rp_of_odd_lags` asks for `PlaqReflPositive` at a lag `lag`, and
`plaqReflPositive_odd_of_crossing` supplies it at a lag of the form `a + a + 1`. Two facts are needed
to join them and neither was stated:

* every odd lag at even extent IS of that form (`ActionSplit.even_sub_one_of_odd` and
  `ActionSplit.exists_fixed_site` together), and
* the plane can be CHOSEN so that the base plaquette lies in the positive half — the odd-lag
  analogue of `ActionSplit.exists_half_below`, and sharper than it, because a link reflection needs
  `0 < lv ≤ m` rather than `lv < m`: the transverse family sits one step above the axis family.

`exists_odd_lag_plane_in_half` is both at once. The two solutions of `2x = lag − 1` differ by `m`
(`ActionSplit.lv_other_half`), so one of them always lands the site in `(0, m]`: a site at level `0`
goes to level `m`, and a site above `m` drops by `m`. -/

section OddPlane

variable {d n : ℕ} [NeZero n] (m : ℕ)

/-- **EVERY ODD LAG AT EVEN EXTENT HAS A PLANE, AND THE PLANE CAN BE CHOSEN TO PUT A GIVEN SITE IN
THE POSITIVE HALF.**

`a + a + 1 = c` says the reflection is the link reflection Part B is about; `0 < lv a p ≤ m` says the
site `p` sits at a transverse level of `oblkS`. Both solutions of `2x = c − 1` are available and they
differ by `m`, which is exactly the offset that moves a level out of `{0} ∪ (m, n)` into `(0, m]`.

DERIVED: `1` is the link reflection's one-step offset — the whole difference from a site reflection;
`m` is the half-extent, a parameter. -/
theorem exists_odd_lag_plane_in_half (hn : Even n) (hm : n = 2 * m) (hm0 : 0 < m)
    {c : Fin n} (hc : ¬ Even c.val) (p : Fin n) :
    ∃ a : Fin n, a + a + 1 = c ∧ 0 < lv a p ∧ lv a p ≤ m := by
  have h2 : 2 ≤ n := by omega
  obtain ⟨a0, ha0⟩ := exists_fixed_site (even_sub_one_of_odd hn h2 hc)
  have hcc : ((c - 1) + 1 : Fin n) = c := by simp
  have hj := lv_lt a0 p
  by_cases h : 0 < lv a0 p ∧ lv a0 p ≤ m
  · exact ⟨a0, by rw [ha0, hcc], h.1, h.2⟩
  · have hmm : fcast n m + fcast n m = 0 := by
      rw [fcast_add]
      have hs : m + m = n := by omega
      rw [hs, fcast_self]
    have hcase : lv a0 p = 0 ∨ m < lv a0 p := by omega
    have hlvo : lv (a0 + fcast n m) p = (lv a0 p + m) % n := lv_other_half m hm a0 p
    have hres : 0 < lv (a0 + fcast n m) p ∧ lv (a0 + fcast n m) p ≤ m := by
      rcases hcase with h0 | hgt
      · rw [hlvo, h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
        omega
      · have hmod : (lv a0 p + m) % n = lv a0 p + m - n := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hlvo, hmod]
        omega
    refine ⟨a0 + fcast n m, ?_, hres.1, hres.2⟩
    calc (a0 + fcast n m) + (a0 + fcast n m) + 1
        = ((a0 + a0) + (fcast n m + fcast n m)) + 1 := by abel
      _ = c := by rw [hmm, add_zero, ha0, hcc]

variable (τ : Fin d) (a : Fin n)

/-- **A plaquette with NEITHER direction along the axis, based inside the positive half, reads the
positive half alone.** Its four links all sit at the base site's level, because a transverse step
does not move the axis coordinate — which is why `0 < lv ≤ m` is enough and no `< m` is needed.

This is the locality hypothesis `aObs_local` takes, at the base plaquette
`WilsonBridge.corrClay` reads. -/
theorem transverse_plaq_links_in_oblkS (hm : n = 2 * m) (hm0 : 0 < m) {q₀ : Plaq d n}
    (h1 : q₀.1.1 ≠ τ) (h2 : q₀.1.2 ≠ τ) (hlv : 0 < lv a (q₀.2 τ)) (hle : lv a (q₀.2 τ) ≤ m) :
    ∀ l ∈ (bd q₀).map Prod.fst, l ∈ oblkS τ a m :=
  oplaq_links_plus τ a m hm hm0 ((mem_oplqPlus τ a m q₀).mpr
    ⟨fun hc => h1 hc.1, hlv, hle, fun hc => absurd hc (fun hd => hd.elim h1 h2)⟩)

end OddPlane

/-! ### The whole reduction, in one statement -/

section Collapse

open MassGap.ReflectPositive

/-- **THE AXIOM AT EVEN EXTENT, REDUCED TO ONE INEQUALITY PER PLANE.**

`corrClay_rp_of_odd_lags` left `PlaqReflPositive` at the odd lags as a hypothesis. This consumes
instead the CROSSING INTEGRAL at each plane, with the locality of the base plaquette SUPPLIED rather
than assumed — so the caller's obligation is exactly the object
`CrossingIntegration.wilson_crossing_pairing_nonneg` proves in the abstract, and nothing else about
the lattice remains between the two.

What is still not here is the identification of that integrand with the crossing theorem's: Part E
factors the measure, Part F transports the mirror, Part G supplies the instances, and what remains is
to exhibit the straddling factor as `exp (β' · hsRe (X (act g x)) (X y))` for the block-diagonal word
`X` of Parts C and D. `integral_oblk_mirror` is the change of variables that identification is
performed in.

DERIVED: `3` is the gauge group's rank, `4` the dimension, `(0, 1)` the base plaquette's plane and
`2` the lag axis — all of them `WilsonBridge.corrClay`'s own choices, not this file's. -/
theorem corrClay_rp_of_crossing (Nap m : ℕ) (hm : Nap + 1 = 2 * m) (hm0 : 0 < m) (β : ℝ)
    (hcross : ∀ a : Fin (Nap + 1),
      (∀ l ∈ (bd ((((0 : Fin 4), (1 : Fin 4)),
          (fun _ => 0 : Site 4 (Nap + 1))) : Plaq 4 (Nap + 1))).map Prod.fst,
        l ∈ oblkS (2 : Fin 4) a m) →
      ∀ aC : ℝ, 0 ≤ ∫ U,
        aObs (N := 3) (2 : Fin 4) a m
            ((((0 : Fin 4), (1 : Fin 4)), (fun _ => 0 : Site 4 (Nap + 1))) : Plaq 4 (Nap + 1))
            β aC U
          * aObs (2 : Fin 4) a m
              ((((0 : Fin 4), (1 : Fin 4)), (fun _ => 0 : Site 4 (Nap + 1))) : Plaq 4 (Nap + 1))
              β aC (reflConf (2 : Fin 4) (a + a + 1) U)
          * Real.exp (-β * actCrossO (2 : Fin 4) a m U)
        ∂(cvol (Link 4 (Nap + 1)) (probHaar (MassGap.SUN.SU 3)))) :
    (∀ lag, 0 ≤ MassGap.WilsonBridge.corrClay (Nap + 1) β lag)
      ∧ 0 < ∑ lag, MassGap.WilsonBridge.corrClay (Nap + 1) β lag := by
  refine corrClay_rp_of_odd_lags Nap m hm hm0 β (fun lag hodd => ?_)
  have hn : Even (Nap + 1) := ⟨m, by omega⟩
  obtain ⟨a, ha, hlv0, hlvm⟩ :=
    exists_odd_lag_plane_in_half m hn hm hm0 hodd (0 : Fin (Nap + 1))
  have hloc : ∀ l ∈ (bd ((((0 : Fin 4), (1 : Fin 4)),
      (fun _ => 0 : Site 4 (Nap + 1))) : Plaq 4 (Nap + 1))).map Prod.fst,
      l ∈ oblkS (2 : Fin 4) a m :=
    transverse_plaq_links_in_oblkS m (2 : Fin 4) a hm hm0
      (by decide : (0 : Fin 4) ≠ (2 : Fin 4)) (by decide : (1 : Fin 4) ≠ (2 : Fin 4))
      hlv0 hlvm
  have hRP := plaqReflPositive_odd_of_crossing (N := 3) (2 : Fin 4) a m
    (by norm_num) hm hm0 β _ (hcross a hloc)
  rwa [ha] at hRP

end Collapse

/-! ## Part I — the straddling family, block by block

The blocks of the direct sum are indexed by `oplqCross` ITSELF, not by a reduced family. That is the
cheap way to do it: `oplqCross` carries both orientations of every geometric plaquette, and summing
over it double-counts each one — but the double count is harmless, because the two orientations
contribute the SAME `Re tr` (`re_tr_hol_swap`: their words are inverse) and the direct sum simply
carries the block twice. No bijection, no fibre counting, no factor to track.

Each `q ∈ oplqCross` reads four links in fixed roles: `aLinkOf` and `bLinkOf` are its two fixed axis
links (the plane gauge), `sLinkOf` is the link the POSITIVE half owns and `tLinkOf` the one the mirror
owns. Which of the two transverse links is which depends on the plane — at level `0` the positive
half owns the far one, at level `m` the near one — and that is the same swap the handedness
reconciliation is about. After inverting the plane variables on the UPPER plane alone (`uplane`,
licensed by `invLink_measurePreserving`) both planes read one shape:

    Re tr (word) = hsRe (g̃(A) · U(S) · g̃(B)⁻¹) (U(T))

`re_tr_hol_cross` is that identity, uniformly over `oplqCross`.

`planeARaw` and `planeBRaw` run the assignment BACKWARDS — from a half-link to the plane links of the
plaquette that owns it — which is what makes the gauge a genuine action on `oblkS → SU N` rather
than a family indexed by blocks. **That inverse assignment needs `2 ≤ m`**, and it is the only place
the restriction is used: at `m = 1` the level-`1` and level-`m` families coincide, one half-link is
owned by two different plaquettes with different plane links, and no coordinatewise action exists.
`negctl_plane_assignment_collides_at_m_one` exhibits the collision. -/

section Family

variable {d n : ℕ} [NeZero n] {N : ℕ}
variable (τ : Fin d) (a : Fin n) (m : ℕ)

/-- **A site is at level zero exactly when it IS the plane's base site.**

DERIVED: `0` is the level of `a` itself, which is what `lv` measures from. -/
theorem lv_eq_zero_iff (a p : Fin n) : lv a p = 0 ↔ p = a := by
  constructor
  · intro h
    have hp := eq_add_lv a p
    rw [h, fcast_zero, add_zero] at hp
    exact hp
  · intro h
    subst h
    simp [lv]

/-- One step BACK along the axis — the inverse of `WilsonHypercubic.shift` in the axis direction.

DERIVED: `1` is one lattice step, the same `1` as in `shift`. -/
def backSite (τ : Fin d) (x : Site d n) : Site d n := Function.update x τ (x τ - 1)

theorem backSite_shift (τ : Fin d) (x : Site d n) : backSite τ (shift τ x) = x := by
  funext k
  show (Function.update (shift τ x) τ ((shift τ x) τ - 1)) k = x k
  by_cases h : k = τ
  · rw [h, Function.update_self]
    have hs : (shift τ x) τ = x τ + 1 := by
      show (Function.update x τ (x τ + 1)) τ = x τ + 1
      rw [Function.update_self]
    rw [hs]
    abel
  · rw [Function.update_of_ne h]
    show (Function.update x τ (x τ + 1)) k = x k
    rw [Function.update_of_ne h]

/-- **The transverse direction of a straddling plaquette** — the one that is not the axis.

DERIVED: no numeral; the projections are structure fields. -/
def cDir (τ : Fin d) (q : Plaq d n) : Fin d := if q.1.1 = τ then q.1.2 else q.1.1

theorem cDir_left (ν : Fin d) (x : Site d n) : cDir τ (((τ, ν), x) : Plaq d n) = ν := by
  show (if τ = τ then ν else τ) = ν
  rw [if_pos rfl]

theorem cDir_right {ν : Fin d} (hν : ν ≠ τ) (x : Site d n) :
    cDir τ (((ν, τ), x) : Plaq d n) = ν := by
  show (if ν = τ then τ else ν) = ν
  rw [if_neg hν]

theorem cDir_ne {q : Plaq d n} (hq : q ∈ oplqCross τ a m) : cDir τ q ≠ τ := by
  obtain ⟨hdeg, hax, -⟩ := (mem_oplqCross τ a m q).mp hq
  show (if q.1.1 = τ then q.1.2 else q.1.1) ≠ τ
  by_cases h : q.1.1 = τ
  · rw [if_pos h]
    exact fun hc => hdeg ⟨h, hc⟩
  · rw [if_neg h]
    exact h

/-- **The upper plane** — the fixed axis links at level `m`. Inverting the gauge variable on THESE
links and nowhere else is what puts the two planes into one handedness
(`cross_word_uniform_on_plane` against `cross_word_uniform_off_plane`).

DERIVED: `m` is the upper plane's level, a parameter of the geometry, not a chosen cut. -/
def uplane (τ : Fin d) (a : Fin n) (m : ℕ) : Finset (Link d n) :=
  (oblkR τ a m).filter (fun l => lv a (l.2 τ) = m)

theorem mem_uplane (l : Link d n) :
    l ∈ uplane τ a m ↔ (l ∈ oblkR τ a m ∧ lv a (l.2 τ) = m) := by
  rw [uplane, Finset.mem_filter]

/-- The link of the POSITIVE half that a straddling plaquette owns: the far transverse link at the
lower plane, the near one at the upper.

DERIVED: `0` is the lower plane's level and `m` the upper one's; both are the geometry. -/
def sLinkOf (τ : Fin d) (a : Fin n) (q : Plaq d n) : Link d n :=
  if lv a (q.2 τ) = 0 then (cDir τ q, shift τ q.2) else (cDir τ q, q.2)

/-- The link of the MIRROR that a straddling plaquette owns — the other transverse one.

DERIVED: `0` is the lower plane's level. -/
def tLinkOf (τ : Fin d) (a : Fin n) (q : Plaq d n) : Link d n :=
  if lv a (q.2 τ) = 0 then (cDir τ q, q.2) else (cDir τ q, shift τ q.2)

/-- The plaquette's first fixed axis link.

DERIVED: no numeral. -/
def aLinkOf (τ : Fin d) (q : Plaq d n) : Link d n := (τ, q.2)

/-- The plaquette's second fixed axis link — one transverse step along.

DERIVED: no numeral. -/
def bLinkOf (τ : Fin d) (q : Plaq d n) : Link d n := (τ, shift (cDir τ q) q.2)

theorem aLinkOf_mem {q : Plaq d n} (hq : q ∈ oplqCross τ a m) : aLinkOf τ q ∈ oblkR τ a m := by
  rw [mem_oblkR]
  exact ⟨rfl, ((mem_oplqCross τ a m q).mp hq).2.2⟩

theorem bLinkOf_mem {q : Plaq d n} (hq : q ∈ oplqCross τ a m) : bLinkOf τ q ∈ oblkR τ a m := by
  have hν : cDir τ q ≠ τ := cDir_ne τ a m hq
  rw [mem_oblkR]
  refine ⟨rfl, ?_⟩
  show lv a ((shift (cDir τ q) q.2) τ) = 0 ∨ lv a ((shift (cDir τ q) q.2) τ) = m
  rw [lv_shift_of_ne hν]
  exact ((mem_oplqCross τ a m q).mp hq).2.2

theorem sLinkOf_mem (hm : n = 2 * m) (hm0 : 0 < m) {q : Plaq d n} (hq : q ∈ oplqCross τ a m) :
    sLinkOf τ a q ∈ oblkS τ a m := by
  have hn : 0 < n := NeZero.pos n
  have hν : cDir τ q ≠ τ := cDir_ne τ a m hq
  have hlev := ((mem_oplqCross τ a m q).mp hq).2.2
  show (if lv a (q.2 τ) = 0 then ((cDir τ q, shift τ q.2) : Link d n)
      else (cDir τ q, q.2)) ∈ oblkS τ a m
  by_cases h0 : lv a (q.2 τ) = 0
  · rw [if_pos h0, mem_oblkS, if_neg hν]
    show 0 < lv a ((shift τ q.2) τ) ∧ lv a ((shift τ q.2) τ) ≤ m
    rw [lv_shift_axis, h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hmm : lv a (q.2 τ) = m := hlev.resolve_left h0
    rw [if_neg h0, mem_oblkS, if_neg hν]
    show 0 < lv a (q.2 τ) ∧ lv a (q.2 τ) ≤ m
    omega

theorem tLinkOf_mem (hm : n = 2 * m) (hm0 : 0 < m) {q : Plaq d n} (hq : q ∈ oplqCross τ a m) :
    tLinkOf τ a q ∈ oblkT τ a m := by
  have hn : 0 < n := NeZero.pos n
  have hν : cDir τ q ≠ τ := cDir_ne τ a m hq
  have hlev := ((mem_oplqCross τ a m q).mp hq).2.2
  show (if lv a (q.2 τ) = 0 then ((cDir τ q, q.2) : Link d n)
      else (cDir τ q, shift τ q.2)) ∈ oblkT τ a m
  by_cases h0 : lv a (q.2 τ) = 0
  · rw [if_pos h0, mem_oblkT, if_neg hν]
    exact Or.inl h0
  · have hmm : lv a (q.2 τ) = m := hlev.resolve_left h0
    rw [if_neg h0, mem_oblkT, if_neg hν]
    show lv a ((shift τ q.2) τ) = 0 ∨ m < lv a ((shift τ q.2) τ)
    rw [lv_shift_axis, hmm]
    rcases Nat.lt_or_ge (m + 1) n with hlt | hge
    · exact Or.inr (by rw [Nat.mod_eq_of_lt hlt]; omega)
    · have he : m + 1 = n := by omega
      exact Or.inl (by rw [he, Nat.mod_self])

/-- **THE MIRROR TRANSPORT MATCHES THE BLOCKS.** The reflection carries a straddling plaquette's
MIRROR link to its own POSITIVE-half link — at the lower plane because the base site is `a` itself,
at the upper because `m + m = n` makes the half-extent its own negative. So the second argument of
the cross form is the SAME word evaluated at the transported variable, which is what
`wilson_crossing_pairing_nonneg` reads.

DERIVED: no numeral beyond the geometry's own `a + a + 1`. -/
theorem reflLink_tLinkOf (hm : n = 2 * m) (hm0 : 0 < m) {q : Plaq d n}
    (hq : q ∈ oplqCross τ a m) :
    reflLink τ (a + a + 1) (tLinkOf τ a q) = sLinkOf τ a q := by
  have hν : cDir τ q ≠ τ := cDir_ne τ a m hq
  have hlev := ((mem_oplqCross τ a m q).mp hq).2.2
  have hcancel : (a + a + 1 : Fin n) - 1 = a + a := by simp
  show reflLink τ (a + a + 1)
      (if lv a (q.2 τ) = 0 then ((cDir τ q, q.2) : Link d n) else (cDir τ q, shift τ q.2))
    = (if lv a (q.2 τ) = 0 then ((cDir τ q, shift τ q.2) : Link d n) else (cDir τ q, q.2))
  by_cases h0 : lv a (q.2 τ) = 0
  · rw [if_pos h0, if_pos h0]
    have hz : q.2 τ = a := (lv_eq_zero_iff a (q.2 τ)).mp h0
    show ((cDir τ q, if cDir τ q = τ then reflSite τ ((a + a + 1) - 1) q.2
        else reflSite τ (a + a + 1) q.2) : Link d n) = (cDir τ q, shift τ q.2)
    rw [if_neg hν]
    refine congrArg (fun z => ((cDir τ q, z) : Link d n)) ?_
    funext j
    by_cases hj : j = τ
    · rw [hj]
      have hsh : (shift τ q.2) τ = a + 1 := by
        show (Function.update q.2 τ (q.2 τ + 1)) τ = a + 1
        rw [Function.update_self, hz]
      rw [reflSite_axis, hsh, hz]
      abel
    · have hsh : (shift τ q.2) j = q.2 j := by
        show (Function.update q.2 τ (q.2 τ + 1)) j = q.2 j
        rw [Function.update_of_ne hj]
      rw [reflSite_of_ne hj, hsh]
  · have hmm : lv a (q.2 τ) = m := hlev.resolve_left h0
    rw [if_neg h0, if_neg h0]
    have hmz : fcast n m + fcast n m = 0 := by
      rw [fcast_add]
      have hs : m + m = n := by omega
      rw [hs, fcast_self]
    have hz : q.2 τ = a + fcast n m := by
      have hp := eq_add_lv a (q.2 τ)
      rwa [hmm] at hp
    show ((cDir τ q, if cDir τ q = τ then reflSite τ ((a + a + 1) - 1) (shift τ q.2)
        else reflSite τ (a + a + 1) (shift τ q.2)) : Link d n) = (cDir τ q, q.2)
    rw [if_neg hν, reflSite_shift_axis, hcancel]
    refine congrArg (fun z => ((cDir τ q, z) : Link d n)) ?_
    funext j
    by_cases hj : j = τ
    · rw [hj]
      have hneg : -(fcast n m) = fcast n m := (eq_neg_of_add_eq_zero_right hmz).symm
      rw [reflSite_axis, hz]
      calc a + a - (a + fcast n m) = a + (-(fcast n m)) := by abel
        _ = a + fcast n m := by rw [hneg]
    · rw [reflSite_of_ne hj]

/-! ### One `Re tr` per block, in one handedness -/

/-- **The two orientations of a straddling plaquette contribute the same `Re tr`.** Their boundary
words are inverse to each other and `re_trace_inv` does not see inversion. This is why indexing the
blocks by `oplqCross` itself — orientations and all — costs nothing: the direct sum carries each
geometric plaquette twice and each copy carries the same number.

DERIVED: no numeral. -/
theorem re_tr_hol_swap (τ ν : Fin d) (x : Site d n) (U : Link d n → MassGap.SUN.SU N) :
    (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) (((ν, τ), x) : Plaq d n) U
        : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re
      = (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) (((τ, ν), x) : Plaq d n) U
        : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re := by
  rw [cross_word_left, cross_word_right]
  have hinv : ((U (ν, x) * U (τ, shift ν x) * (U (ν, shift τ x))⁻¹) * (U (τ, x))⁻¹
        : MassGap.SUN.SU N)
      = (((U (τ, x) * U (ν, shift τ x) * (U (τ, shift ν x))⁻¹) * (U (ν, x))⁻¹)⁻¹) := by group
  rw [hinv, re_trace_inv]

/-- **Every straddling plaquette reads the same as its canonical orientation**, the one with the axis
first. -/
theorem re_tr_hol_canon {q : Plaq d n} (hq : q ∈ oplqCross τ a m)
    (U : Link d n → MassGap.SUN.SU N) :
    (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) q U : MassGap.SUN.SU N)
        : Matrix (Fin N) (Fin N) ℂ)).re
      = (Matrix.trace ((wilsonHol (bd (d := d) (n := n))
          (((τ, cDir τ q), q.2) : Plaq d n) U : MassGap.SUN.SU N)
        : Matrix (Fin N) (Fin N) ℂ)).re := by
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  obtain ⟨hdeg, hax, -⟩ := (mem_oplqCross τ a m _).mp hq
  have hdeg' : ¬ (μ = τ ∧ ν = τ) := hdeg
  rcases hax with hμ | hν
  · have hμ' : μ = τ := hμ
    have hcd : cDir τ (((μ, ν), x) : Plaq d n) = ν := by
      show (if μ = τ then ν else μ) = ν
      rw [if_pos hμ']
    rw [hcd, hμ']
  · have hν' : ν = τ := hν
    have hμne : μ ≠ τ := fun hc => hdeg' ⟨hc, hν'⟩
    have hcd : cDir τ (((μ, ν), x) : Plaq d n) = μ := by
      show (if μ = τ then ν else μ) = μ
      rw [if_neg hμne]
    rw [hcd, hν']
    exact re_tr_hol_swap τ μ x U

/-- **THE STRADDLING WORD, AT THE CANONICAL ORIENTATION, IN ONE HANDEDNESS.**

With the gauge variables of the UPPER plane inverted and nowhere else, both fixed planes read

    hsRe (g̃(A) · U(S) · g̃(B)⁻¹) (U(T))

— `cross_word_uniform_off_plane` at the lower plane, `cross_word_uniform_on_plane` at the upper. The
two transverse links exchange roles between the planes, and `sLinkOf`/`tLinkOf` carry that exchange.

DERIVED: `0` is the lower plane's level and `m` the upper one's. -/
theorem re_tr_hol_cross_explicit (hm : n = 2 * m) (hm0 : 0 < m) {ν : Fin d} (hν : ν ≠ τ)
    {x : Site d n} (hlev : lv a (x τ) = 0 ∨ lv a (x τ) = m)
    (U : Link d n → MassGap.SUN.SU N) :
    (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) (((τ, ν), x) : Plaq d n) U
        : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re
      = hsRe (((invLink (uplane τ a m) U (τ, x)
              * U (if lv a (x τ) = 0 then ((ν, shift τ x) : Link d n) else (ν, x))
              * (invLink (uplane τ a m) U (τ, shift ν x))⁻¹ : MassGap.SUN.SU N))
            : Matrix (Fin N) (Fin N) ℂ)
          ((U (if lv a (x τ) = 0 then ((ν, x) : Link d n) else (ν, shift τ x))
            : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  have hlvtr : lv a ((shift ν x) τ) = lv a (x τ) := lv_shift_of_ne hν a x
  by_cases h0 : lv a (x τ) = 0
  · have hA : ((τ, x) : Link d n) ∉ uplane τ a m := by
      rw [mem_uplane]
      rintro ⟨-, h⟩
      have h' : lv a (x τ) = m := h
      omega
    have hB : ((τ, shift ν x) : Link d n) ∉ uplane τ a m := by
      rw [mem_uplane]
      rintro ⟨-, h⟩
      have h' : lv a ((shift ν x) τ) = m := h
      rw [hlvtr] at h'
      omega
    rw [if_pos h0, if_pos h0]
    exact cross_word_uniform_off_plane τ ν x (uplane τ a m) hA hB U
  · have hmm : lv a (x τ) = m := hlev.resolve_left h0
    have hA : ((τ, x) : Link d n) ∈ uplane τ a m := by
      rw [mem_uplane, mem_oblkR]
      exact ⟨⟨rfl, Or.inr hmm⟩, hmm⟩
    have hB : ((τ, shift ν x) : Link d n) ∈ uplane τ a m := by
      have h' : lv a ((shift ν x) τ) = m := by rw [hlvtr]; exact hmm
      rw [mem_uplane, mem_oblkR]
      exact ⟨⟨rfl, Or.inr h'⟩, h'⟩
    rw [if_neg h0, if_neg h0]
    exact cross_word_uniform_on_plane τ ν x (uplane τ a m) hA hB U

/-- **ONE FORMULA FOR EVERY BLOCK.** The straddling plaquette's contribution, in the roles
`aLinkOf`, `bLinkOf`, `sLinkOf`, `tLinkOf` — orientation and plane both absorbed.

DERIVED: no numeral. -/
theorem re_tr_hol_cross (hm : n = 2 * m) (hm0 : 0 < m) {q : Plaq d n}
    (hq : q ∈ oplqCross τ a m) (U : Link d n → MassGap.SUN.SU N) :
    (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) q U : MassGap.SUN.SU N)
        : Matrix (Fin N) (Fin N) ℂ)).re
      = hsRe (((invLink (uplane τ a m) U (aLinkOf τ q) * U (sLinkOf τ a q)
            * (invLink (uplane τ a m) U (bLinkOf τ q))⁻¹ : MassGap.SUN.SU N))
            : Matrix (Fin N) (Fin N) ℂ)
          ((U (tLinkOf τ a q) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  rw [re_tr_hol_canon τ a m hq U]
  exact re_tr_hol_cross_explicit τ a m hm hm0 (cDir_ne τ a m hq)
    ((mem_oplqCross τ a m q).mp hq).2.2 U

/-! ### The assignment run BACKWARDS — and where `2 ≤ m` is needed -/

/-- The default plane link — the axis link at level `0` through the plane's own base site. A half-link
that is the positive-half link of no straddling plaquette is assigned this, and the gauge then acts on
it by conjugation; the word does not read it, so the value is immaterial and only its membership
matters.

DERIVED: `a` is the plane's base site, the caller's; no numeral is chosen. -/
def dfltPlane (τ : Fin d) (a : Fin n) : Link d n := (τ, fun _ => a)

theorem dfltPlane_mem : dfltPlane τ a ∈ oblkR τ a m := by
  rw [mem_oblkR]
  refine ⟨rfl, Or.inl ?_⟩
  show lv a ((fun _ => a : Site d n) τ) = 0
  simp [lv]

/-- **A level-one site is one step above the plane.** -/
theorem lv_sub_one_of_lv_one {a p : Fin n} (h : lv a p = 1) : lv a (p - 1) = 0 := by
  have hb := lv_add_one a (p - 1)
  rw [sub_add_cancel, h] at hb
  have hj : lv a (p - 1) < n := lv_lt a (p - 1)
  rcases Nat.lt_or_ge (lv a (p - 1) + 1) n with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hb; omega
  · have he : lv a (p - 1) + 1 = n := by omega
    rw [he, Nat.mod_self] at hb
    omega

/-- **The first plane link of the straddling plaquette that owns a given half-link.**

Run backwards from the link: a transverse link at level `1` is the far link of a plaquette based at
the LOWER plane, one at level `m` is the near link of a plaquette based at the UPPER plane. Those two
cases are disjoint exactly when `1 ≠ m`, which is `2 ≤ m`; at `m = 1` one link is owned by two
plaquettes with different plane links and no assignment exists
(`negctl_plane_assignment_collides_at_m_one`).

DERIVED: `1` is the level one step above the lower plane — a lattice step, not a cut; `m` is the
upper plane's level, a parameter. -/
def planeARaw (τ : Fin d) (a : Fin n) (m : ℕ) (l : Link d n) : Link d n :=
  if l.1 = τ then dfltPlane τ a
  else if lv a (l.2 τ) = 1 then (τ, backSite τ l.2)
  else if lv a (l.2 τ) = m then (τ, l.2)
  else dfltPlane τ a

/-- The second plane link of the same plaquette — one transverse step along.

DERIVED: `1` and `m` are the two straddling levels, as in `planeARaw`. -/
def planeBRaw (τ : Fin d) (a : Fin n) (m : ℕ) (l : Link d n) : Link d n :=
  if l.1 = τ then dfltPlane τ a
  else if lv a (l.2 τ) = 1 then (τ, shift l.1 (backSite τ l.2))
  else if lv a (l.2 τ) = m then (τ, shift l.1 l.2)
  else dfltPlane τ a

theorem planeARaw_mem (l : Link d n) : planeARaw τ a m l ∈ oblkR τ a m := by
  show (if l.1 = τ then dfltPlane τ a
    else if lv a (l.2 τ) = 1 then ((τ, backSite τ l.2) : Link d n)
    else if lv a (l.2 τ) = m then (τ, l.2)
    else dfltPlane τ a) ∈ oblkR τ a m
  by_cases h1 : l.1 = τ
  · rw [if_pos h1]
    exact dfltPlane_mem τ a m
  · rw [if_neg h1]
    by_cases h2 : lv a (l.2 τ) = 1
    · rw [if_pos h2, mem_oblkR]
      refine ⟨rfl, Or.inl ?_⟩
      show lv a ((backSite τ l.2) τ) = 0
      have hb : (backSite τ l.2) τ = l.2 τ - 1 := by
        show (Function.update l.2 τ (l.2 τ - 1)) τ = l.2 τ - 1
        rw [Function.update_self]
      rw [hb]
      exact lv_sub_one_of_lv_one h2
    · rw [if_neg h2]
      by_cases h3 : lv a (l.2 τ) = m
      · rw [if_pos h3, mem_oblkR]
        exact ⟨rfl, Or.inr h3⟩
      · rw [if_neg h3]
        exact dfltPlane_mem τ a m

theorem planeBRaw_mem (l : Link d n) : planeBRaw τ a m l ∈ oblkR τ a m := by
  show (if l.1 = τ then dfltPlane τ a
    else if lv a (l.2 τ) = 1 then ((τ, shift l.1 (backSite τ l.2)) : Link d n)
    else if lv a (l.2 τ) = m then (τ, shift l.1 l.2)
    else dfltPlane τ a) ∈ oblkR τ a m
  by_cases h1 : l.1 = τ
  · rw [if_pos h1]
    exact dfltPlane_mem τ a m
  · rw [if_neg h1]
    by_cases h2 : lv a (l.2 τ) = 1
    · rw [if_pos h2, mem_oblkR]
      refine ⟨rfl, Or.inl ?_⟩
      show lv a ((shift l.1 (backSite τ l.2)) τ) = 0
      rw [lv_shift_of_ne h1]
      have hb : (backSite τ l.2) τ = l.2 τ - 1 := by
        show (Function.update l.2 τ (l.2 τ - 1)) τ = l.2 τ - 1
        rw [Function.update_self]
      rw [hb]
      exact lv_sub_one_of_lv_one h2
    · rw [if_neg h2]
      by_cases h3 : lv a (l.2 τ) = m
      · rw [if_pos h3, mem_oblkR]
        refine ⟨rfl, Or.inr ?_⟩
        show lv a ((shift l.1 l.2) τ) = m
        rw [lv_shift_of_ne h1]
        exact h3
      · rw [if_neg h3]
        exact dfltPlane_mem τ a m

/-- **THE BACKWARD ASSIGNMENT RECOVERS THE BLOCK'S OWN PLANE LINK** — and this is the one statement
in the development that needs `2 ≤ m`, i.e. extent at least four. At `m = 1` the two straddling
families sit at the same level and the assignment is not well defined. -/
theorem planeARaw_sLinkOf (hm : n = 2 * m) (hm2 : 2 ≤ m) {q : Plaq d n}
    (hq : q ∈ oplqCross τ a m) : planeARaw τ a m (sLinkOf τ a q) = aLinkOf τ q := by
  have hn : 0 < n := NeZero.pos n
  have hν : cDir τ q ≠ τ := cDir_ne τ a m hq
  have hlev := ((mem_oplqCross τ a m q).mp hq).2.2
  by_cases h0 : lv a (q.2 τ) = 0
  · have hsL : sLinkOf τ a q = ((cDir τ q, shift τ q.2) : Link d n) := by
      show (if lv a (q.2 τ) = 0 then ((cDir τ q, shift τ q.2) : Link d n)
        else (cDir τ q, q.2)) = (cDir τ q, shift τ q.2)
      rw [if_pos h0]
    have hlv1 : lv a ((shift τ q.2) τ) = 1 := by
      rw [lv_shift_axis, h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [hsL]
    show (if (cDir τ q) = τ then dfltPlane τ a
      else if lv a ((shift τ q.2) τ) = 1 then ((τ, backSite τ (shift τ q.2)) : Link d n)
      else if lv a ((shift τ q.2) τ) = m then (τ, shift τ q.2)
      else dfltPlane τ a) = aLinkOf τ q
    rw [if_neg hν, if_pos hlv1, backSite_shift]
    rfl
  · have hmm : lv a (q.2 τ) = m := hlev.resolve_left h0
    have hsL : sLinkOf τ a q = ((cDir τ q, q.2) : Link d n) := by
      show (if lv a (q.2 τ) = 0 then ((cDir τ q, shift τ q.2) : Link d n)
        else (cDir τ q, q.2)) = (cDir τ q, q.2)
      rw [if_neg h0]
    have hne1 : lv a (q.2 τ) ≠ 1 := by omega
    rw [hsL]
    show (if (cDir τ q) = τ then dfltPlane τ a
      else if lv a (q.2 τ) = 1 then ((τ, backSite τ q.2) : Link d n)
      else if lv a (q.2 τ) = m then (τ, q.2)
      else dfltPlane τ a) = aLinkOf τ q
    rw [if_neg hν, if_neg hne1, if_pos hmm]
    rfl

theorem planeBRaw_sLinkOf (hm : n = 2 * m) (hm2 : 2 ≤ m) {q : Plaq d n}
    (hq : q ∈ oplqCross τ a m) : planeBRaw τ a m (sLinkOf τ a q) = bLinkOf τ q := by
  have hn : 0 < n := NeZero.pos n
  have hν : cDir τ q ≠ τ := cDir_ne τ a m hq
  have hlev := ((mem_oplqCross τ a m q).mp hq).2.2
  by_cases h0 : lv a (q.2 τ) = 0
  · have hsL : sLinkOf τ a q = ((cDir τ q, shift τ q.2) : Link d n) := by
      show (if lv a (q.2 τ) = 0 then ((cDir τ q, shift τ q.2) : Link d n)
        else (cDir τ q, q.2)) = (cDir τ q, shift τ q.2)
      rw [if_pos h0]
    have hlv1 : lv a ((shift τ q.2) τ) = 1 := by
      rw [lv_shift_axis, h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [hsL]
    show (if (cDir τ q) = τ then dfltPlane τ a
      else if lv a ((shift τ q.2) τ) = 1
        then ((τ, shift (cDir τ q) (backSite τ (shift τ q.2))) : Link d n)
      else if lv a ((shift τ q.2) τ) = m then (τ, shift (cDir τ q) (shift τ q.2))
      else dfltPlane τ a) = bLinkOf τ q
    rw [if_neg hν, if_pos hlv1, backSite_shift]
    rfl
  · have hmm : lv a (q.2 τ) = m := hlev.resolve_left h0
    have hsL : sLinkOf τ a q = ((cDir τ q, q.2) : Link d n) := by
      show (if lv a (q.2 τ) = 0 then ((cDir τ q, shift τ q.2) : Link d n)
        else (cDir τ q, q.2)) = (cDir τ q, q.2)
      rw [if_neg h0]
    have hne1 : lv a (q.2 τ) ≠ 1 := by omega
    rw [hsL]
    show (if (cDir τ q) = τ then dfltPlane τ a
      else if lv a (q.2 τ) = 1 then ((τ, shift (cDir τ q) (backSite τ q.2)) : Link d n)
      else if lv a (q.2 τ) = m then (τ, shift (cDir τ q) q.2)
      else dfltPlane τ a) = bLinkOf τ q
    rw [if_neg hν, if_neg hne1, if_pos hmm]
    rfl

end Family

section FamilyControl

/-- **NEGATIVE CONTROL — THE BACKWARD ASSIGNMENT COLLIDES AT `m = 1`, AND THE RESTRICTION TO
`2 ≤ m` IS NOT DECORATION.**

At extent `2` the level one step above the lower plane IS the upper plane, so a single transverse
link of the positive half is the half-link of TWO different straddling plaquettes — and their plane
links differ, so no map from half-links to plane links can serve both. The gauge is then not a
coordinatewise action of the plane group on the half, and `planeAct` cannot be used.

Exhibited at `d = 2`, extent `2`, axis `0`, plane base `0`, `m = 1`: the plaquettes based at the site
`(0, 0)` and at the site `(1, 0)` share the positive-half link `(1, (1, 0))` and read different
plane links.

DERIVED: `2` is the smallest even extent and `1` its half; `0` and `1` are two distinct directions
and the two sites they separate. All are the smallest instance of the collision, not a tuning. -/
theorem negctl_plane_assignment_collides_at_m_one :
    ∃ q₁ q₂ : Plaq 2 2,
      q₁ ∈ oplqCross (0 : Fin 2) (0 : Fin 2) 1
        ∧ q₂ ∈ oplqCross (0 : Fin 2) (0 : Fin 2) 1
        ∧ sLinkOf (0 : Fin 2) (0 : Fin 2) q₁ = sLinkOf (0 : Fin 2) (0 : Fin 2) q₂
        ∧ aLinkOf (0 : Fin 2) q₁ ≠ aLinkOf (0 : Fin 2) q₂ := by
  refine ⟨(((0 : Fin 2), (1 : Fin 2)), (fun _ => 0 : Site 2 2)),
    (((0 : Fin 2), (1 : Fin 2)),
      (Function.update (fun _ => 0) (0 : Fin 2) 1 : Site 2 2)), ?_, ?_, ?_, ?_⟩
  · rw [mem_oplqCross]; decide
  · rw [mem_oplqCross]; decide
  · decide
  · decide

end FamilyControl

/-! ## Part J — the word, and the straddling sum as ONE cross form

`crossWord` is the block-diagonal of the positive half's straddling links, indexed by `oplqCross`
itself. `planeA` and `planeB` are the backward assignment of Part I, so the plane group acts on the
half by `planeAct` and `crossWord` is invariant under it (`hsRe_crossWord_planeAct`, which is
`hsRe_dsum_conj` pointed at this family).

`sum_re_tr_oplqCross` is the payoff: the whole straddling sum, at the configuration assembled from
the three block variables AND with the upper plane's gauge inverted, is

    hsRe (crossWord (planeAct planeA planeB g x)) (crossWord y)

— one cross form, one word, two independent half-variables and the plane group acting on one of them.
That is the integrand of `CrossingIntegration.wilson_crossing_pairing_nonneg` and nothing else. -/

section Word

variable {d n : ℕ} [NeZero n] {N : ℕ}
variable (τ : Fin d) (a : Fin n) (m : ℕ)

/-- The first plane link of the plaquette owning a half-link, as an element of the plane block.

DERIVED: no numeral; the membership is `planeARaw_mem`. -/
def planeA (l : ↥(oblkS τ a m)) : ↥(oblkR τ a m) :=
  ⟨planeARaw τ a m (l : Link d n), planeARaw_mem τ a m _⟩

/-- The second one.

DERIVED: no numeral. -/
def planeB (l : ↥(oblkS τ a m)) : ↥(oblkR τ a m) :=
  ⟨planeBRaw τ a m (l : Link d n), planeBRaw_mem τ a m _⟩

/-- A block's own half-link, as an index of the positive half.

DERIVED: no numeral. -/
def sIdx (hm : n = 2 * m) (hm0 : 0 < m) (k : ↥(oplqCross τ a m)) : ↥(oblkS τ a m) :=
  ⟨sLinkOf τ a (k : Plaq d n), sLinkOf_mem τ a m hm hm0 k.2⟩

/-- **THE WORD THE CROSSING INTEGRATION READS.** The direct sum, over the straddling plaquettes, of
the positive half's link at each — relabelled to a `Fin` because that is the type
`wilson_crossing_pairing_nonneg` takes.

DERIVED: no numeral; the size is `Fintype.card (Fin N × oplqCross)`, a count. -/
noncomputable def crossWord (hm : n = 2 * m) (hm0 : 0 < m)
    (u : ↥(oblkS τ a m) → MassGap.SUN.SU N) :
    Matrix (Fin (Fintype.card (Fin N × ↥(oplqCross τ a m))))
      (Fin (Fintype.card (Fin N × ↥(oplqCross τ a m)))) ℂ :=
  (Matrix.blockDiagonal (fun k : ↥(oplqCross τ a m) =>
      ((u (sIdx τ a m hm hm0 k) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ))).submatrix
    (Fintype.equivFin (Fin N × ↥(oplqCross τ a m))).symm
    (Fintype.equivFin (Fin N × ↥(oplqCross τ a m))).symm

theorem hsRe_crossWord (hm : n = 2 * m) (hm0 : 0 < m)
    (u v : ↥(oblkS τ a m) → MassGap.SUN.SU N) :
    hsRe (crossWord τ a m hm hm0 u) (crossWord τ a m hm hm0 v)
      = ∑ k : ↥(oplqCross τ a m),
          hsRe ((u (sIdx τ a m hm hm0 k) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
            ((v (sIdx τ a m hm hm0 k) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) :=
  hsRe_blockDiagonal_fin _ _

/-- **THE WORD DOES NOT SEE THE PLANE GAUGE** — `hXinv`. Each block is conjugated by its own pair of
plane links and `hsRe_conj` absorbs them one block at a time; this is `hsRe_dsum_conj` pointed at the
lattice's own family.

DERIVED: no numeral. -/
theorem hsRe_crossWord_planeAct (hm : n = 2 * m) (hm0 : 0 < m)
    (g : ↥(oblkR τ a m) → MassGap.SUN.SU N) (u v : ↥(oblkS τ a m) → MassGap.SUN.SU N) :
    hsRe (crossWord τ a m hm hm0 (planeAct (planeA τ a m) (planeB τ a m) g u))
        (crossWord τ a m hm hm0 (planeAct (planeA τ a m) (planeB τ a m) g v))
      = hsRe (crossWord τ a m hm hm0 u) (crossWord τ a m hm hm0 v) := by
  rw [hsRe_crossWord, hsRe_crossWord]
  exact Finset.sum_congr rfl (fun k _ => hsRe_conj _ _ _ _)

/-- **EVERY COORDINATE OF THE WORD IS BOUNDED BY ONE** — `hXb`. -/
theorem abs_coord_crossWord_le_one (hm : n = 2 * m) (hm0 : 0 < m)
    (p : Coord (Fintype.card (Fin N × ↥(oplqCross τ a m))))
    (u : ↥(oblkS τ a m) → MassGap.SUN.SU N) :
    |coord p (crossWord τ a m hm hm0 u)| ≤ 1 :=
  abs_coord_le_one_of_entries
    (fun i j => entry_blockDiagonal_fin_norm_le_one
      (fun k => u (sIdx τ a m hm hm0 k)) i j) p

/-! ### The straddling sum, block by block -/

theorem invLink_invLink (R : Finset (Link d n)) (U : Link d n → MassGap.SUN.SU N) :
    invLink R (invLink R U) = U := by
  funext l
  show (if l ∈ R then (invLink R U l)⁻¹ else invLink R U l) = U l
  by_cases h : l ∈ R
  · rw [if_pos h]
    show ((if l ∈ R then (U l)⁻¹ else U l))⁻¹ = U l
    rw [if_pos h, inv_inv]
  · rw [if_neg h]
    show (if l ∈ R then (U l)⁻¹ else U l) = U l
    rw [if_neg h]

theorem invLink_of_not_mem (R : Finset (Link d n)) (U : Link d n → MassGap.SUN.SU N)
    {l : Link d n} (hl : l ∉ R) : invLink R U l = U l := by
  show (if l ∈ R then (U l)⁻¹ else U l) = U l
  rw [if_neg hl]

/-- The three block restrictions of `joinO`, in the form the word identity needs. -/
theorem joinO_mem_R (g : ↥(oblkR τ a m) → MassGap.SUN.SU N)
    (x : ↥(oblkS τ a m) → MassGap.SUN.SU N) (y : ↥(oblkT τ a m) → MassGap.SUN.SU N)
    {l : Link d n} (hl : l ∈ oblkR τ a m) : joinO τ a m g x y l = g ⟨l, hl⟩ :=
  join3_mem_R (oblkR τ a m) (oblkS τ a m) (oblkT τ a m)
    (oblkS_disjoint_oblkR τ a m).symm (oblkT_disjoint_oblkR τ a m).symm
    (oblkS_disjoint_oblkT τ a m) (oblk_cover τ a m) g x y hl

theorem joinO_mem_S (g : ↥(oblkR τ a m) → MassGap.SUN.SU N)
    (x : ↥(oblkS τ a m) → MassGap.SUN.SU N) (y : ↥(oblkT τ a m) → MassGap.SUN.SU N)
    {l : Link d n} (hl : l ∈ oblkS τ a m) : joinO τ a m g x y l = x ⟨l, hl⟩ :=
  join3_mem_S (oblkR τ a m) (oblkS τ a m) (oblkT τ a m)
    (oblkS_disjoint_oblkR τ a m).symm (oblkT_disjoint_oblkR τ a m).symm
    (oblkS_disjoint_oblkT τ a m) (oblk_cover τ a m) g x y hl

theorem joinO_mem_T (g : ↥(oblkR τ a m) → MassGap.SUN.SU N)
    (x : ↥(oblkS τ a m) → MassGap.SUN.SU N) (y : ↥(oblkT τ a m) → MassGap.SUN.SU N)
    {l : Link d n} (hl : l ∈ oblkT τ a m) : joinO τ a m g x y l = y ⟨l, hl⟩ :=
  join3_mem_T (oblkR τ a m) (oblkS τ a m) (oblkT τ a m)
    (oblkS_disjoint_oblkR τ a m).symm (oblkT_disjoint_oblkR τ a m).symm
    (oblkS_disjoint_oblkT τ a m) (oblk_cover τ a m) g x y hl

theorem tLinkOf_dir {q : Plaq d n} : (tLinkOf τ a q).1 = cDir τ q := by
  show (if lv a (q.2 τ) = 0 then ((cDir τ q, q.2) : Link d n)
    else (cDir τ q, shift τ q.2)).1 = cDir τ q
  by_cases h0 : lv a (q.2 τ) = 0
  · rw [if_pos h0]
  · rw [if_neg h0]

/-- **ONE BLOCK'S CONTRIBUTION, IN THE CROSSING INTEGRATION'S VARIABLES.**

At the configuration assembled from the three block variables, with the upper plane's gauge inverted,
a straddling plaquette reads the cross form of the gauge-acted positive-half variable against the
mirror's — and the mirror's, transported, IS the second half-variable.

DERIVED: no numeral. -/
theorem re_tr_hol_block (hm : n = 2 * m) (hm0 : 0 < m) (hm2 : 2 ≤ m)
    (g : ↥(oblkR τ a m) → MassGap.SUN.SU N) (x y : ↥(oblkS τ a m) → MassGap.SUN.SU N)
    (k : ↥(oplqCross τ a m)) :
    (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) (k : Plaq d n)
        (invLink (uplane τ a m) (joinO τ a m g x (mirrorT τ a m hm hm0 y)))
        : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re
      = hsRe (((planeAct (planeA τ a m) (planeB τ a m) g x (sIdx τ a m hm hm0 k)
            : MassGap.SUN.SU N)) : Matrix (Fin N) (Fin N) ℂ)
          ((y (sIdx τ a m hm hm0 k) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  have hq : (k : Plaq d n) ∈ oplqCross τ a m := k.2
  have hν : cDir τ (k : Plaq d n) ≠ τ := cDir_ne τ a m hq
  have haR : aLinkOf τ (k : Plaq d n) ∈ oblkR τ a m := aLinkOf_mem τ a m hq
  have hbR : bLinkOf τ (k : Plaq d n) ∈ oblkR τ a m := bLinkOf_mem τ a m hq
  have hsS : sLinkOf τ a (k : Plaq d n) ∈ oblkS τ a m := sLinkOf_mem τ a m hm hm0 hq
  have htT : tLinkOf τ a (k : Plaq d n) ∈ oblkT τ a m := tLinkOf_mem τ a m hm hm0 hq
  have hup : ∀ l : Link d n, l ∈ uplane τ a m → l ∈ oblkR τ a m :=
    fun l h => ((mem_uplane τ a m l).mp h).1
  have hsNot : sLinkOf τ a (k : Plaq d n) ∉ uplane τ a m := fun hc =>
    (Finset.disjoint_left.mp (oblkS_disjoint_oblkR τ a m)) hsS (hup _ hc)
  have htNot : tLinkOf τ a (k : Plaq d n) ∉ uplane τ a m := fun hc =>
    (Finset.disjoint_left.mp (oblkT_disjoint_oblkR τ a m)) htT (hup _ hc)
  rw [re_tr_hol_cross τ a m hm hm0 hq, invLink_invLink,
    invLink_of_not_mem _ _ hsNot, invLink_of_not_mem _ _ htNot,
    joinO_mem_R τ a m g x _ haR, joinO_mem_R τ a m g x _ hbR,
    joinO_mem_S τ a m g x _ hsS, joinO_mem_T τ a m g x _ htT]
  have hmirT : mirrorT τ a m hm hm0 y ⟨tLinkOf τ a (k : Plaq d n), htT⟩
      = y (sIdx τ a m hm hm0 k) := by
    have hne : (tLinkOf τ a (k : Plaq d n)).1 ≠ τ := by
      rw [tLinkOf_dir]; exact hν
    have heq : (mirrorEquivTS τ a m hm hm0) ⟨tLinkOf τ a (k : Plaq d n), htT⟩
        = sIdx τ a m hm hm0 k :=
      Subtype.ext (reflLink_tLinkOf τ a m hm hm0 hq)
    show (if (tLinkOf τ a (k : Plaq d n)).1 = τ
        then (y ((mirrorEquivTS τ a m hm hm0) ⟨tLinkOf τ a (k : Plaq d n), htT⟩))⁻¹
        else y ((mirrorEquivTS τ a m hm hm0) ⟨tLinkOf τ a (k : Plaq d n), htT⟩))
      = y (sIdx τ a m hm hm0 k)
    rw [if_neg hne, heq]
  have hpa : (⟨aLinkOf τ (k : Plaq d n), haR⟩ : ↥(oblkR τ a m))
      = planeA τ a m (sIdx τ a m hm hm0 k) :=
    Subtype.ext (planeARaw_sLinkOf τ a m hm hm2 hq).symm
  have hpb : (⟨bLinkOf τ (k : Plaq d n), hbR⟩ : ↥(oblkR τ a m))
      = planeB τ a m (sIdx τ a m hm hm0 k) :=
    Subtype.ext (planeBRaw_sLinkOf τ a m hm hm2 hq).symm
  rw [hmirT, hpa, hpb]
  rfl

/-- **THE WHOLE STRADDLING SUM IS ONE CROSS FORM.**

`oplqCross` indexes the blocks directly, so the sum over the Finset is the sum over the block index,
and `hsRe_crossWord` folds it into a single `hsRe`. Both orientations of every geometric plaquette
appear and both carry the same number; the direct sum simply has the block twice.

DERIVED: no numeral. -/
theorem sum_re_tr_oplqCross (hm : n = 2 * m) (hm0 : 0 < m) (hm2 : 2 ≤ m)
    (g : ↥(oblkR τ a m) → MassGap.SUN.SU N) (x y : ↥(oblkS τ a m) → MassGap.SUN.SU N) :
    (∑ q ∈ oplqCross τ a m, (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) q
        (invLink (uplane τ a m) (joinO τ a m g x (mirrorT τ a m hm hm0 y)))
        : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re)
      = hsRe (crossWord τ a m hm hm0 (planeAct (planeA τ a m) (planeB τ a m) g x))
          (crossWord τ a m hm hm0 y) := by
  rw [← Finset.sum_coe_sort (oplqCross τ a m)
    (fun q => (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) q
      (invLink (uplane τ a m) (joinO τ a m g x (mirrorT τ a m hm hm0 y)))
      : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re), hsRe_crossWord]
  exact Finset.sum_congr rfl (fun k _ => re_tr_hol_block τ a m hm hm0 hm2 g x y k)

end Word

/-! ## Part K — the observable as a function of the half, and the odd-lag inequality

`aObs` reads the whole configuration; `aHalf` is the same thing as a function of `oblkS` alone, which
is the `a : Ω → ℝ` the crossing integration takes. `aObs_local` with
`transverse_plaq_links_in_oblkS` is what makes the two agree.

`odd_crossing_integral_nonneg` is the discharge: the odd-lag pairing integral is nonnegative. It
carries two hypotheses beyond the geometry of Part B, and both are real:

* `2 ≤ m` — extent at least four, because the backward plane assignment collides at `m = 1`
  (`negctl_plane_assignment_collides_at_m_one`); and
* `0 ≤ β` — because the Wilson cross kernel `exp(β' · hsRe)` is positive-semidefinite only for
  `β' ≥ 0`, which `CrossingIntegration.NegControl.su3_kernel_nonneg_iff` shows cannot be dropped.
  This is physics, not bookkeeping: at negative coupling the weight is not reflection positive at a
  link reflection. -/

section Observable

variable {d n : ℕ} [NeZero n] {N : ℕ}
variable (τ : Fin d) (a : Fin n) (m : ℕ)

/-- Extend a half-configuration to the whole lattice by the identity. The extension's values off the
positive half are immaterial: `aObs` reads `oblkS` alone once the base plaquette does.

DERIVED: `1` is the group identity, which is what a link no one reads carries. -/
noncomputable def extendS (x : ↥(oblkS τ a m) → MassGap.SUN.SU N) :
    Link d n → MassGap.SUN.SU N :=
  fun l => if h : l ∈ oblkS τ a m then x ⟨l, h⟩ else 1

theorem extendS_mem (x : ↥(oblkS τ a m) → MassGap.SUN.SU N) {l : Link d n}
    (hl : l ∈ oblkS τ a m) : extendS τ a m x l = x ⟨l, hl⟩ := by
  show (if h : l ∈ oblkS τ a m then x ⟨l, h⟩ else 1) = x ⟨l, hl⟩
  rw [dif_pos hl]

theorem measurable_extendS : Measurable (extendS (N := N) τ a m) := by
  refine measurable_pi_lambda _ (fun l => ?_)
  by_cases h : l ∈ oblkS τ a m
  · have he : (fun x : ↥(oblkS τ a m) → MassGap.SUN.SU N => extendS τ a m x l)
        = fun x => x ⟨l, h⟩ := funext (fun x => extendS_mem τ a m x h)
    rw [he]
    exact measurable_pi_apply _
  · have he : (fun x : ↥(oblkS τ a m) → MassGap.SUN.SU N => extendS τ a m x l)
        = fun _ => (1 : MassGap.SUN.SU N) := by
      funext x
      show (if h' : l ∈ oblkS τ a m then x ⟨l, h'⟩ else 1) = 1
      rw [dif_neg h]
    rw [he]
    exact measurable_const

/-- **The observable, as a function of the positive half alone** — the crossing integration's `a`.

DERIVED: no numeral. -/
noncomputable def aHalf (q₀ : Plaq d n) (β aC : ℝ)
    (x : ↥(oblkS τ a m) → MassGap.SUN.SU N) : ℝ :=
  aObs (N := N) τ a m q₀ β aC (extendS τ a m x)

theorem measurable_aObs (q₀ : Plaq d n) (β aC : ℝ) :
    Measurable (aObs (N := N) τ a m q₀ β aC) := by
  show Measurable (fun U : Link d n → MassGap.SUN.SU N =>
    (MassGap.WilsonAction.wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) - aC)
      * Real.exp (-β * actPlusO τ a m U))
  exact ((measurable_density_hol q₀).sub measurable_const).mul
    ((measurable_const.mul (measurable_actSum (oplqPlus τ a m))).exp)

theorem measurable_aHalf (q₀ : Plaq d n) (β aC : ℝ) :
    Measurable (aHalf (N := N) τ a m q₀ β aC) :=
  (measurable_aObs τ a m q₀ β aC).comp (measurable_extendS τ a m)

/-- **The observable is bounded** — `hab`. The plaquette energy lies in `[0, 2]` and the half's
Boltzmann factor is bounded by the exponential of the half's own cardinality.

DERIVED: `2` is the range of `WilsonAction.wilsonDensity`, computed there, and the card is a count. -/
theorem abs_aObs_le (hN : N ≠ 0) (q₀ : Plaq d n) (β aC : ℝ)
    (U : Link d n → MassGap.SUN.SU N) :
    |aObs (N := N) τ a m q₀ β aC U|
      ≤ (2 + |aC|) * Real.exp (|β| * (2 * (oplqPlus τ a m).card)) := by
  show |(MassGap.WilsonAction.wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) - aC)
      * Real.exp (-β * actPlusO τ a m U)| ≤ _
  rw [abs_mul]
  have hD0 : 0 ≤ MassGap.WilsonAction.wilsonDensity
      (wilsonHol (bd (d := d) (n := n)) q₀ U) :=
    MassGap.WilsonAction.wilsonDensity_nonneg hN _
  have hD2 : MassGap.WilsonAction.wilsonDensity
      (wilsonHol (bd (d := d) (n := n)) q₀ U) ≤ 2 :=
    MassGap.WilsonAction.wilsonDensity_le_two hN _
  have hfirst : |MassGap.WilsonAction.wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) - aC|
      ≤ 2 + |aC| := by
    rw [abs_le]
    constructor
    · have := neg_abs_le aC
      have := le_abs_self aC
      linarith
    · have := neg_abs_le aC
      have := le_abs_self aC
      linarith
  have hsecond : |Real.exp (-β * actPlusO (N := N) τ a m U)|
      ≤ Real.exp (|β| * (2 * (oplqPlus τ a m).card)) := by
    rw [abs_of_nonneg (Real.exp_nonneg _)]
    refine Real.exp_le_exp.mpr ?_
    have hA : |actPlusO (N := N) τ a m U| ≤ 2 * (oplqPlus τ a m).card :=
      abs_actSum_le hN _ U
    calc -β * actPlusO (N := N) τ a m U ≤ |(-β) * actPlusO (N := N) τ a m U| := le_abs_self _
      _ = |β| * |actPlusO (N := N) τ a m U| := by rw [abs_mul, abs_neg]
      _ ≤ |β| * (2 * (oplqPlus τ a m).card) := mul_le_mul_of_nonneg_left hA (abs_nonneg β)
  exact mul_le_mul hfirst hsecond (abs_nonneg _) (by positivity)

theorem abs_aHalf_le (hN : N ≠ 0) (q₀ : Plaq d n) (β aC : ℝ)
    (x : ↥(oblkS τ a m) → MassGap.SUN.SU N) :
    |aHalf (N := N) τ a m q₀ β aC x|
      ≤ (2 + |aC|) * Real.exp (|β| * (2 * (oplqPlus τ a m).card)) :=
  abs_aObs_le τ a m hN q₀ β aC _

/-- **The straddling factor is bounded.**

DERIVED: `2` is the range of `WilsonAction.wilsonDensity`; the card is a count. -/
theorem abs_exp_actCrossO_le (hN : N ≠ 0) (β : ℝ) (U : Link d n → MassGap.SUN.SU N) :
    |Real.exp (-β * actCrossO (N := N) τ a m U)|
      ≤ Real.exp (|β| * (2 * (oplqCross τ a m).card)) := by
  rw [abs_of_nonneg (Real.exp_nonneg _)]
  refine Real.exp_le_exp.mpr ?_
  have hA : |actCrossO (N := N) τ a m U| ≤ 2 * (oplqCross τ a m).card := abs_actSum_le hN _ U
  calc -β * actCrossO (N := N) τ a m U ≤ |(-β) * actCrossO (N := N) τ a m U| := le_abs_self _
    _ = |β| * |actCrossO (N := N) τ a m U| := by rw [abs_mul, abs_neg]
    _ ≤ |β| * (2 * (oplqCross τ a m).card) := mul_le_mul_of_nonneg_left hA (abs_nonneg β)

/-! ### Coordinate measurability of the word -/

theorem continuous_su_entry {Nc : ℕ} (i j : Fin Nc) :
    Continuous (fun s : MassGap.SUN.SU Nc => ((s : Matrix (Fin Nc) (Fin Nc) ℂ)) i j) :=
  continuous_subtype_val.matrix_elem i j

theorem measurable_coord_of_entries {γ : Type} [MeasurableSpace γ] {Nc : ℕ}
    (M : γ → Matrix (Fin Nc) (Fin Nc) ℂ)
    (h : ∀ i j, Measurable (fun v => M v i j)) (p : Coord Nc) :
    Measurable (fun v => coord p (M v)) := by
  by_cases hb : p.2.2 = true
  · have he : (fun v => coord p (M v)) = fun v => (M v p.1 p.2.1).re := by
      funext v
      show (if p.2.2 = true then (M v p.1 p.2.1).re else (M v p.1 p.2.1).im) = _
      rw [if_pos hb]
    rw [he]
    exact Complex.measurable_re.comp (h _ _)
  · have he : (fun v => coord p (M v)) = fun v => (M v p.1 p.2.1).im := by
      funext v
      show (if p.2.2 = true then (M v p.1 p.2.1).re else (M v p.1 p.2.1).im) = _
      rw [if_neg hb]
    rw [he]
    exact Complex.measurable_im.comp (h _ _)

/-- **EVERY ENTRY OF A BLOCK-DIAGONAL OF `SU(N)` MATRICES IS MEASURABLE IN THE FAMILY** — it is one
unitary entry on the diagonal blocks and the constant `0` off them.

Stated on the abstract family, like `entry_blockDiagonal_fin_norm_le_one` beside it, because the
argument never looks at what indexes the blocks.

DERIVED: `0` is the off-block entry; the size is `Fintype.card (Fin N × K)`, a count. -/
theorem measurable_entry_blockDiagonal_fin {K : Type} [Fintype K] [DecidableEq K] {N : ℕ}
    {γ : Type} [MeasurableSpace γ] (W : γ → K → MassGap.SUN.SU N)
    (hW : ∀ k, Measurable (fun v => W v k))
    (i j : Fin (Fintype.card (Fin N × K))) :
    Measurable (fun v : γ =>
      ((Matrix.blockDiagonal (fun k : K =>
          ((W v k : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ))).submatrix
        (Fintype.equivFin (Fin N × K)).symm (Fintype.equivFin (Fin N × K)).symm) i j) := by
  by_cases hk : ((Fintype.equivFin (Fin N × K)).symm i).2
      = ((Fintype.equivFin (Fin N × K)).symm j).2
  · have he : (fun v : γ =>
        ((Matrix.blockDiagonal (fun k : K =>
            ((W v k : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ))).submatrix
          (Fintype.equivFin (Fin N × K)).symm (Fintype.equivFin (Fin N × K)).symm) i j)
        = fun v => ((W v ((Fintype.equivFin (Fin N × K)).symm i).2 : MassGap.SUN.SU N)
            : Matrix (Fin N) (Fin N) ℂ)
            ((Fintype.equivFin (Fin N × K)).symm i).1
            ((Fintype.equivFin (Fin N × K)).symm j).1 := by
      funext v
      show Matrix.blockDiagonal (fun k : K =>
          ((W v k : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ))
          ((Fintype.equivFin (Fin N × K)).symm i)
          ((Fintype.equivFin (Fin N × K)).symm j) = _
      rw [Matrix.blockDiagonal_apply, if_pos hk]
    rw [he]
    exact (continuous_su_entry _ _).measurable.comp (hW _)
  · have he : (fun v : γ =>
        ((Matrix.blockDiagonal (fun k : K =>
            ((W v k : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ))).submatrix
          (Fintype.equivFin (Fin N × K)).symm (Fintype.equivFin (Fin N × K)).symm) i j)
        = fun _ => (0 : ℂ) := by
      funext v
      show Matrix.blockDiagonal (fun k : K =>
          ((W v k : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ))
          ((Fintype.equivFin (Fin N × K)).symm i)
          ((Fintype.equivFin (Fin N × K)).symm j) = _
      rw [Matrix.blockDiagonal_apply, if_neg hk]
    rw [he]
    exact measurable_const

#print axioms measurable_entry_blockDiagonal_fin

theorem measurable_entry_crossWord (hm : n = 2 * m) (hm0 : 0 < m)
    (i j : Fin (Fintype.card (Fin N × ↥(oplqCross τ a m)))) :
    Measurable (fun u : ↥(oblkS τ a m) → MassGap.SUN.SU N =>
      crossWord τ a m hm hm0 u i j) :=
  measurable_entry_blockDiagonal_fin
    (fun (u : ↥(oblkS τ a m) → MassGap.SUN.SU N) (k : ↥(oplqCross τ a m)) =>
      u (sIdx τ a m hm hm0 k)) (fun _ => measurable_pi_apply _) i j

theorem measurable_coord_crossWord (hm : n = 2 * m) (hm0 : 0 < m)
    (p : Coord (Fintype.card (Fin N × ↥(oplqCross τ a m)))) :
    Measurable (fun u : ↥(oblkS τ a m) → MassGap.SUN.SU N =>
      coord p (crossWord τ a m hm hm0 u)) :=
  measurable_coord_of_entries _ (measurable_entry_crossWord τ a m hm hm0) p

/-! ### The integrand, with the upper plane's gauge inverted -/

/-- The odd-lag integrand, with the upper plane's gauge variables inverted inside the straddling
factor. The substitution is `invLink_measurePreserving`'s and leaves the two observables alone,
because they read `oblkS` and its mirror, neither of which meets the plane.

DERIVED: no numeral. -/
noncomputable def oddIntegrand (q₀ : Plaq d n) (β aC : ℝ)
    (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  aObs τ a m q₀ β aC U * aObs τ a m q₀ β aC (reflConf τ (a + a + 1) U)
    * Real.exp (-β * actCrossO τ a m (invLink (uplane τ a m) U))

theorem measurable_oddIntegrand (q₀ : Plaq d n) (β aC : ℝ) :
    Measurable (oddIntegrand (N := N) τ a m q₀ β aC) :=
  ((measurable_aObs τ a m q₀ β aC).mul
      ((measurable_aObs τ a m q₀ β aC).comp
        (reflConf_measurePreserving (N := N) τ (a + a + 1)).measurable)).mul
    ((measurable_const.mul ((measurable_actSum (oplqCross τ a m)).comp
      (invLink_measurePreserving (N := N) (uplane τ a m)).measurable)).exp)

theorem abs_oddIntegrand_le (hN : N ≠ 0) (q₀ : Plaq d n) (β aC : ℝ)
    (U : Link d n → MassGap.SUN.SU N) :
    |oddIntegrand (N := N) τ a m q₀ β aC U|
      ≤ ((2 + |aC|) * Real.exp (|β| * (2 * (oplqPlus τ a m).card)))
        * ((2 + |aC|) * Real.exp (|β| * (2 * (oplqPlus τ a m).card)))
        * Real.exp (|β| * (2 * (oplqCross τ a m).card)) := by
  show |aObs τ a m q₀ β aC U * aObs τ a m q₀ β aC (reflConf τ (a + a + 1) U)
      * Real.exp (-β * actCrossO τ a m (invLink (uplane τ a m) U))| ≤ _
  rw [abs_mul, abs_mul]
  refine mul_le_mul (mul_le_mul (abs_aObs_le τ a m hN q₀ β aC U)
    (abs_aObs_le τ a m hN q₀ β aC _) (abs_nonneg _) (by positivity))
    (abs_exp_actCrossO_le τ a m hN β _) (abs_nonneg _) (by positivity)

/-- **The substitution on the upper plane leaves the two observables alone.** Both read the positive
half or its mirror, and the plane meets neither. -/
theorem integral_odd_eq_oddIntegrand (hN : N ≠ 0) (hm : n = 2 * m) (hm0 : 0 < m)
    (q₀ : Plaq d n) (hq₀ : ∀ l ∈ (bd q₀).map Prod.fst, l ∈ oblkS τ a m) (β aC : ℝ) :
    (∫ U, aObs (N := N) τ a m q₀ β aC U
        * aObs τ a m q₀ β aC (reflConf τ (a + a + 1) U)
        * Real.exp (-β * actCrossO τ a m U)
        ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))))
      = ∫ U, oddIntegrand (N := N) τ a m q₀ β aC U
        ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))) := by
  have hFm : Measurable (fun U : Link d n → MassGap.SUN.SU N =>
      aObs (N := N) τ a m q₀ β aC U * aObs τ a m q₀ β aC (reflConf τ (a + a + 1) U)
        * Real.exp (-β * actCrossO τ a m U)) :=
    ((measurable_aObs τ a m q₀ β aC).mul
        ((measurable_aObs τ a m q₀ β aC).comp
          (reflConf_measurePreserving (N := N) τ (a + a + 1)).measurable)).mul
      ((measurable_const.mul (measurable_actSum (oplqCross τ a m))).exp)
  rw [← integral_comp_of_mp (invLink_measurePreserving (N := N) (uplane τ a m)) hFm]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
  -- the plane meets neither the positive half nor its mirror
  have hoff : ∀ l : Link d n, l ∈ oblkS τ a m →
      invLink (uplane τ a m) U l = U l := by
    intro l hl
    refine invLink_of_not_mem _ _ (fun hc => ?_)
    exact (Finset.disjoint_left.mp (oblkS_disjoint_oblkR τ a m)) hl
      ((mem_uplane τ a m l).mp hc).1
  have hoffT : ∀ l : Link d n, l ∈ oblkT τ a m →
      invLink (uplane τ a m) U l = U l := by
    intro l hl
    refine invLink_of_not_mem _ _ (fun hc => ?_)
    exact (Finset.disjoint_left.mp (oblkT_disjoint_oblkR τ a m)) hl
      ((mem_uplane τ a m l).mp hc).1
  have h1 : aObs (N := N) τ a m q₀ β aC (invLink (uplane τ a m) U)
      = aObs τ a m q₀ β aC U :=
    aObs_local τ a m hm hm0 q₀ hq₀ β aC _ _ hoff
  have h2 : aObs (N := N) τ a m q₀ β aC
      (reflConf τ (a + a + 1) (invLink (uplane τ a m) U))
      = aObs τ a m q₀ β aC (reflConf τ (a + a + 1) U) := by
    refine aObs_local τ a m hm hm0 q₀ hq₀ β aC _ _ (fun l hl => ?_)
    have hT : reflLink τ (a + a + 1) l ∈ oblkT τ a m := oblkS_maps_oblkT τ a m hm hm0 hl
    show (if l.1 = τ then (invLink (uplane τ a m) U (reflLink τ (a + a + 1) l))⁻¹
        else invLink (uplane τ a m) U (reflLink τ (a + a + 1) l))
      = (if l.1 = τ then (U (reflLink τ (a + a + 1) l))⁻¹
        else U (reflLink τ (a + a + 1) l))
    rw [hoffT _ hT]
  show aObs τ a m q₀ β aC (invLink (uplane τ a m) U)
      * aObs τ a m q₀ β aC (reflConf τ (a + a + 1) (invLink (uplane τ a m) U))
      * Real.exp (-β * actCrossO τ a m (invLink (uplane τ a m) U)) = _
  rw [h1, h2]
  rfl

/-- **THE INTEGRAND, IN THE CROSSING INTEGRATION'S VARIABLES.** -/
theorem oddIntegrand_join (hN : N ≠ 0) (hm : n = 2 * m) (hm0 : 0 < m) (hm2 : 2 ≤ m)
    (q₀ : Plaq d n) (hq₀ : ∀ l ∈ (bd q₀).map Prod.fst, l ∈ oblkS τ a m) (β aC : ℝ)
    (g : ↥(oblkR τ a m) → MassGap.SUN.SU N) (x y : ↥(oblkS τ a m) → MassGap.SUN.SU N) :
    oddIntegrand (N := N) τ a m q₀ β aC (joinO τ a m g x (mirrorT τ a m hm hm0 y))
      = Real.exp (-β * ((oplqCross τ a m).card : ℝ))
        * (aHalf τ a m q₀ β aC x * aHalf τ a m q₀ β aC y
          * Real.exp ((β / (N : ℝ))
            * hsRe (crossWord τ a m hm hm0 (planeAct (planeA τ a m) (planeB τ a m) g x))
                (crossWord τ a m hm hm0 y))) := by
  have h1 : aObs (N := N) τ a m q₀ β aC (joinO τ a m g x (mirrorT τ a m hm hm0 y))
      = aHalf τ a m q₀ β aC x :=
    aObs_local τ a m hm hm0 q₀ hq₀ β aC _ _
      (fun l hl => by rw [joinO_mem_S τ a m g x _ hl, extendS_mem τ a m x hl])
  have h2 : aObs (N := N) τ a m q₀ β aC
      (reflConf τ (a + a + 1) (joinO τ a m g x (mirrorT τ a m hm hm0 y)))
      = aHalf τ a m q₀ β aC y :=
    aObs_local τ a m hm hm0 q₀ hq₀ β aC _ _
      (fun l hl => by
        rw [reflConf_joinO_mirror τ a m hm hm0 g x y hl, extendS_mem τ a m y hl])
  have h3 : actCrossO (N := N) τ a m
      (invLink (uplane τ a m) (joinO τ a m g x (mirrorT τ a m hm hm0 y)))
      = ((oplqCross τ a m).card : ℝ)
        - (1 / (N : ℝ)) * hsRe (crossWord τ a m hm hm0
            (planeAct (planeA τ a m) (planeB τ a m) g x)) (crossWord τ a m hm hm0 y) := by
    rw [actCrossO_eq_trace_sum τ a m hN, sum_re_tr_oplqCross τ a m hm hm0 hm2 g x y]
  show aObs τ a m q₀ β aC (joinO τ a m g x (mirrorT τ a m hm hm0 y))
      * aObs τ a m q₀ β aC (reflConf τ (a + a + 1) (joinO τ a m g x (mirrorT τ a m hm hm0 y)))
      * Real.exp (-β * actCrossO τ a m
          (invLink (uplane τ a m) (joinO τ a m g x (mirrorT τ a m hm hm0 y)))) = _
  rw [h1, h2, h3]
  have hexp : Real.exp (-β * (((oplqCross τ a m).card : ℝ)
        - (1 / (N : ℝ)) * hsRe (crossWord τ a m hm hm0
            (planeAct (planeA τ a m) (planeB τ a m) g x)) (crossWord τ a m hm hm0 y)))
      = Real.exp (-β * ((oplqCross τ a m).card : ℝ))
        * Real.exp ((β / (N : ℝ)) * hsRe (crossWord τ a m hm hm0
            (planeAct (planeA τ a m) (planeB τ a m) g x)) (crossWord τ a m hm hm0 y)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- **THE ODD-LAG PAIRING INTEGRAL IS NONNEGATIVE.**

This is the hypothesis `plaqReflPositive_odd_of_crossing` and `corrClay_rp_of_crossing` consume,
discharged: the product Haar factored over the three blocks (Part E), the mirror transported to the
positive half (Part F), the instances (Part G), the family and its word (Parts I and J), and
`CrossingIntegration.wilson_crossing_pairing_nonneg` applied at `β' = β / N`.

Two hypotheses are carried and neither is bookkeeping: `2 ≤ m`, because the backward plane assignment
collides at `m = 1`; and `0 ≤ β`, because the Wilson cross kernel is positive-semidefinite only
there.

DERIVED: `2` is the smallest half-extent at which the plane assignment is single-valued; `0` is the
sign of the coupling the kernel needs and the sign asserted. -/
theorem odd_crossing_integral_nonneg (hN : N ≠ 0) (hm : n = 2 * m) (hm0 : 0 < m) (hm2 : 2 ≤ m)
    {β : ℝ} (hβ : 0 ≤ β) (q₀ : Plaq d n)
    (hq₀ : ∀ l ∈ (bd q₀).map Prod.fst, l ∈ oblkS τ a m) (aC : ℝ) :
    0 ≤ ∫ U, aObs (N := N) τ a m q₀ β aC U
        * aObs τ a m q₀ β aC (reflConf τ (a + a + 1) U)
        * Real.exp (-β * actCrossO τ a m U)
        ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))) := by
  rw [integral_odd_eq_oddIntegrand τ a m hN hm hm0 q₀ hq₀ β aC,
    integral_oblk_mirror τ a m hm hm0 _ (measurable_oddIntegrand τ a m q₀ β aC)
      (abs_oddIntegrand_le τ a m hN q₀ β aC)]
  have hstep : (∫ g, (∫ x, (∫ y, oddIntegrand (N := N) τ a m q₀ β aC
            (joinO τ a m g x (mirrorT τ a m hm hm0 y))
          ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
        ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
      ∂(cvol ↥(oblkR τ a m) (probHaar (MassGap.SUN.SU N))))
      = Real.exp (-β * ((oplqCross τ a m).card : ℝ))
        * ∫ g, (∫ x, (∫ y, aHalf τ a m q₀ β aC x * aHalf τ a m q₀ β aC y
              * Real.exp ((β / (N : ℝ))
                * hsRe (crossWord τ a m hm hm0
                    (planeAct (planeA τ a m) (planeB τ a m) g x))
                  (crossWord τ a m hm hm0 y))
            ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
          ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
        ∂(cvol ↥(oblkR τ a m) (probHaar (MassGap.SUN.SU N))) := by
    have hy : ∀ (g : ↥(oblkR τ a m) → MassGap.SUN.SU N)
        (x : ↥(oblkS τ a m) → MassGap.SUN.SU N),
        (∫ y, oddIntegrand (N := N) τ a m q₀ β aC
            (joinO τ a m g x (mirrorT τ a m hm hm0 y))
          ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
        = Real.exp (-β * ((oplqCross τ a m).card : ℝ))
          * ∫ y, (aHalf τ a m q₀ β aC x * aHalf τ a m q₀ β aC y
              * Real.exp ((β / (N : ℝ))
                * hsRe (crossWord τ a m hm hm0
                    (planeAct (planeA τ a m) (planeB τ a m) g x))
                  (crossWord τ a m hm hm0 y)))
            ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))) := by
      intro g x
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall
        (fun y => oddIntegrand_join τ a m hN hm hm0 hm2 q₀ hq₀ β aC g x y))
    have hx : ∀ g : ↥(oblkR τ a m) → MassGap.SUN.SU N,
        (∫ x, (∫ y, oddIntegrand (N := N) τ a m q₀ β aC
              (joinO τ a m g x (mirrorT τ a m hm hm0 y))
            ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
          ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
        = Real.exp (-β * ((oplqCross τ a m).card : ℝ))
          * ∫ x, (∫ y, (aHalf τ a m q₀ β aC x * aHalf τ a m q₀ β aC y
                * Real.exp ((β / (N : ℝ))
                  * hsRe (crossWord τ a m hm hm0
                      (planeAct (planeA τ a m) (planeB τ a m) g x))
                    (crossWord τ a m hm hm0 y)))
              ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
            ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))) := by
      intro g
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun x => hy g x))
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun g => hx g))
  rw [hstep]
  refine mul_nonneg (Real.exp_nonneg _) ?_
  refine wilson_crossing_pairing_nonneg
    (cvol ↥(oblkR τ a m) (probHaar (MassGap.SUN.SU N)))
    (cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N)))
    (measurable_uncurry_planeAct (planeA τ a m) (planeB τ a m))
    (fun g => planeAct_measurePreserving (planeA τ a m) (planeB τ a m) g)
    (fun g h u => planeAct_mul (planeA τ a m) (planeB τ a m) g h u)
    (crossWord τ a m hm hm0)
    (measurable_coord_crossWord τ a m hm hm0)
    (fun p v => abs_coord_crossWord_le_one τ a m hm hm0 p v)
    (fun g u v => hsRe_crossWord_planeAct τ a m hm hm0 g u v)
    (measurable_aHalf τ a m q₀ β aC) (by positivity)
    (fun x => abs_aHalf_le τ a m hN q₀ β aC x) ?_
  positivity

end Observable

/-! ## THE AXIOM AT EVEN EXTENT — discharged, at extent at least four and nonnegative coupling

`corrClay_rp_of_crossing` reduced the axiom's conclusion to one inequality per plane, with the base
plaquette's locality supplied. `odd_crossing_integral_nonneg` proves that inequality. Composing them
leaves NO hypothesis about the lattice: what remains are the two conditions named in
`odd_crossing_integral_nonneg`'s own statement, and both are properties of the case rather than gaps
in the argument.

* `2 ≤ m`, i.e. extent `Nap + 1 ≥ 4`. At extent `2` the two straddling families read the same
  transverse links (`negctl_plane_assignment_collides_at_m_one`) and the plane gauge is not a
  coordinatewise action. `ActionSplit.exists_even_extent_aperture` picks the aperture from a cofinal
  set, so extents of at least four are exactly as available as extents of at least two.
* `0 ≤ β`. `CharacterExpansion.NegControl.su3_kernel_nonneg_iff` computes the Wilson cross kernel's
  quadratic form on two explicit `SU(3)` elements and finds it nonnegative IF AND ONLY IF `β ≥ 0`.
  At negative coupling the weight is not reflection positive at a link reflection; this is the sign of
  the coupling, not a limitation of the method.

`Complete.wilson_reflection_positive_at` quantifies over EVERY real `β`, so the composite below does
not cover its statement at negative coupling. It covers it at `0 ≤ β`, which is where the theory
lives. -/

section Discharge

open MassGap.ReflectPositive

/-- **THE ODD LAGS, DISCHARGED.** `PlaqReflPositive` at a link-reflection plane, with no hypothesis
left but the geometry, the extent bound and the sign of the coupling.

DERIVED: no numeral beyond `odd_crossing_integral_nonneg`'s own. -/
theorem plaqReflPositive_odd {d n : ℕ} [NeZero n] {N : ℕ} (τ : Fin d) (a : Fin n) (m : ℕ)
    (hN : N ≠ 0) (hm : n = 2 * m) (hm2 : 2 ≤ m) {β : ℝ} (hβ : 0 ≤ β) (q₀ : Plaq d n)
    (hq₀ : ∀ l ∈ (bd q₀).map Prod.fst, l ∈ oblkS τ a m) :
    PlaqReflPositive N τ (a + a + 1) β q₀ :=
  plaqReflPositive_odd_of_crossing τ a m hN hm (by omega) β q₀
    (fun aC => odd_crossing_integral_nonneg τ a m hN hm (by omega) hm2 hβ q₀ hq₀ aC)

/-- **THE CLAY CORRELATION IS REFLECTION POSITIVE AT EVERY EVEN EXTENT OF AT LEAST FOUR, FOR EVERY
NONNEGATIVE COUPLING.**

This is the body of `Complete.wilson_reflection_positive_at` at aperture `Nap`
(`Complete.wilsonCorrAt Nap β` is `WilsonBridge.corrClay (Nap + 1) β` by definition), with NO
hypothesis about the lattice remaining. Every input is proved: the even lags by
`ActionSplit.plaqReflPositive_of_even_lag`, lag zero by `PlaqVariance.corrClay_zero_pos`, and the odd
lags by `plaqReflPositive_odd` — which is the crossing integration applied to the three-block
factorisation of Part E, the mirror transport of Part F and the word of Part J.

DERIVED: `3` is the gauge group's rank and `4` the dimension, both `WilsonBridge.corrClay`'s own; `2`
is the half-extent bound the plane assignment needs and `0` the sign of the coupling the cross kernel
needs. -/
theorem corrClay_reflection_positive (Nap m : ℕ) (hm : Nap + 1 = 2 * m) (hm2 : 2 ≤ m)
    {β : ℝ} (hβ : 0 ≤ β) :
    (∀ lag, 0 ≤ MassGap.WilsonBridge.corrClay (Nap + 1) β lag)
      ∧ 0 < ∑ lag, MassGap.WilsonBridge.corrClay (Nap + 1) β lag :=
  corrClay_rp_of_crossing Nap m hm (by omega) β
    (fun a hloc aC =>
      odd_crossing_integral_nonneg (2 : Fin 4) a m (by norm_num) hm (by omega) hm2 hβ _ hloc aC)

/-- **NEGATIVE CONTROL — the sign of the coupling cannot be dropped.**

`CharacterExpansion.NegControl.su3_kernel_nonneg_iff` evaluates the Wilson cross kernel's quadratic
form on two explicit `SU(3)` elements — the identity and `diag(1, −1, −1)` — and the value is
nonnegative exactly when `β ≥ 0`. That kernel is the one `odd_crossing_integral_nonneg` integrates,
so `0 ≤ β` there is carrying weight: at negative coupling the object the whole odd-lag argument is
about is itself negative on the group the development is built at.

DERIVED: no numeral of this file's; the elements and the value are `CharacterExpansion`'s. -/
theorem negctl_odd_discharge_needs_nonneg_coupling (β : ℝ) :
    0 ≤ (∑ i, ∑ j, MassGap.CharacterExpansion.NegControl.zc i
        * MassGap.CharacterExpansion.NegControl.zc j
        * Real.exp (β * hsRe (MassGap.CharacterExpansion.NegControl.cA i)
            (MassGap.CharacterExpansion.NegControl.cA j))) ↔ 0 ≤ β :=
  MassGap.CharacterExpansion.NegControl.su3_kernel_nonneg_iff β

/-- **NON-VACUITY — the extent bound is met, at the smallest extent that meets it.** Reflection
positivity of the Clay correlation, unconditionally, at extent four and any nonnegative coupling. A
bound no extent satisfied would make `corrClay_reflection_positive` an empty quantification; this is
the witness that it is not.

DERIVED: `3` is the aperture whose extent `3 + 1` is the smallest even extent with `2 ≤ m`, and `2`
is that half. Both are read off the bound, not chosen. -/
theorem corrClay_reflection_positive_at_extent_four {β : ℝ} (hβ : 0 ≤ β) :
    (∀ lag, 0 ≤ MassGap.WilsonBridge.corrClay (3 + 1) β lag)
      ∧ 0 < ∑ lag, MassGap.WilsonBridge.corrClay (3 + 1) β lag :=
  corrClay_reflection_positive 3 2 (by norm_num) (by norm_num) hβ

end Discharge

section AuditN
#print axioms re_tr_hol_swap
#print axioms re_tr_hol_cross
#print axioms planeARaw_sLinkOf
#print axioms planeBRaw_sLinkOf
#print axioms negctl_plane_assignment_collides_at_m_one
#print axioms reflLink_tLinkOf
#print axioms hsRe_crossWord_planeAct
#print axioms abs_coord_crossWord_le_one
#print axioms re_tr_hol_block
#print axioms sum_re_tr_oplqCross
#print axioms measurable_coord_crossWord
#print axioms abs_aObs_le
#print axioms integral_odd_eq_oddIntegrand
#print axioms oddIntegrand_join
#print axioms odd_crossing_integral_nonneg
#print axioms plaqReflPositive_odd
#print axioms corrClay_reflection_positive
#print axioms negctl_odd_discharge_needs_nonneg_coupling
#print axioms corrClay_reflection_positive_at_extent_four
end AuditN

section AuditM
#print axioms exists_odd_lag_plane_in_half
#print axioms transverse_plaq_links_in_oblkS
#print axioms corrClay_rp_of_crossing
end AuditM

section AuditL
#print axioms measurePreserving_relabel_twist
#print axioms oblkT_maps_oblkS
#print axioms mirrorEquivTS
#print axioms measurePreserving_mirrorT
#print axioms reflConf_joinO_mirror
#print axioms negctl_mirrorT_daggers_axis
#print axioms measurable_join3
#print axioms integral_oblk_mirror
#print axioms planeAct_measurePreserving
#print axioms measurable_uncurry_planeAct
#print axioms abs_coord_le_one_of_entries
#print axioms entry_blockDiagonal_fin_norm_le_one
end AuditL

section AuditK
#print axioms blockEquiv3
#print axioms join3_mem_R
#print axioms join3_mem_S
#print axioms join3_mem_T
#print axioms join3_restrict
#print axioms measurePreserving_join3
#print axioms integral_three_block
#print axioms oblk_cover
#print axioms integral_oblk_three_block
#print axioms plane_group_haar
#print axioms oblkR_nonempty
end AuditK

end MassGap.OddLagSplit
