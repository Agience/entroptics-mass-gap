import Mathlib
import MassGap.WilsonHypercubic

/-!
# MassGap.PlaqCount — the plaquette type is ORDERED, so the action counts every plane twice

`WilsonHypercubic.Plaq d n = (Fin d × Fin d) × Site d n` carries an ORDERED pair of directions, so
`((μ,ν),x)` and `((ν,μ),x)` are two distinct elements of the type and `System.action` — a sum over
`Finset.univ : Finset (Plaq d n)` — visits both. Their boundary words are inverse to each other
(`hol_swap`) and `Re tr` does not see inversion on `SU(N)` (`re_trace_inv`), so the two contribute the
SAME Wilson density. The degenerate pairs `μ = ν` contribute nothing (`hol_diag`).

Hence `plaq_ordered_double_counts`: the action density summed over `Plaq` is exactly TWICE the sum
over the planes with `μ < ν`, which is the range the standard Wilson action sums over. The
consequence for the coupling is `boltz_eq_std`:

    (sysWilson N d n).boltz β U = exp (-(2β) · Σ_{μ<ν} φ_W)

so this system's `β` at the Lean normalisation is HALF the standard Wilson `β`:

    β_lean = β_std / 2 .

Nothing downstream changes: every theorem in the development quantifies over `β` (or takes an
interval of it as a hypothesis), and `β ↦ 2β` is a bijection of `[0,∞)` fixing `0`. What the file
supplies is the conversion as a theorem rather than an inference, so that any number read against a
source using the standard normalisation can be converted without re-deriving it.

Build: `python research/code/lean_build.py build MassGap.PlaqCount`.
-/

namespace MassGap.PlaqCount

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonHypercubic
open MassGap.WilsonAction

variable {d n N : ℕ} [NeZero n]

/-! ### The boundary word, and what swapping the two directions does to it -/

/-- **The plaquette holonomy, as the explicit ordered word.** `wilsonHol` is the product of the
boundary word, and `bd` is the four-letter word of the hypercubic plaquette. -/
theorem hol_word (μ ν : Fin d) (x : Site d n) (U : Link d n → MassGap.SUN.SU N) :
    wilsonHol (bd (d := d) (n := n)) (((μ, ν), x) : Plaq d n) U
      = U (μ, x) * U (ν, shift μ x) * (U (μ, shift ν x))⁻¹ * (U (ν, x))⁻¹ := by
  have h : wilsonHol (bd (d := d) (n := n)) (((μ, ν), x) : Plaq d n) U
      = U (μ, x) * (U (ν, shift μ x) * ((U (μ, shift ν x))⁻¹ * ((U (ν, x))⁻¹ * 1))) := rfl
  rw [h]
  group

/-- **The two orderings of one plane have inverse holonomies.** Reading the loop with the directions
swapped traverses the same four links in the opposite order and with opposite orientations, which is
exactly the inverse of the word. -/
theorem hol_swap (μ ν : Fin d) (x : Site d n) (U : Link d n → MassGap.SUN.SU N) :
    wilsonHol (bd (d := d) (n := n)) (((ν, μ), x) : Plaq d n) U
      = (wilsonHol (bd (d := d) (n := n)) (((μ, ν), x) : Plaq d n) U)⁻¹ := by
  rw [hol_word, hol_word]
  group

/-- **A degenerate pair retraces itself**, so its holonomy is the identity. -/
theorem hol_diag (μ : Fin d) (x : Site d n) (U : Link d n → MassGap.SUN.SU N) :
    wilsonHol (bd (d := d) (n := n)) (((μ, μ), x) : Plaq d n) U = 1 := by
  rw [hol_word]
  group

/-- The group inverse of an `SU(N)` element is its conjugate transpose. -/
theorem coe_inv_eq_conjTranspose (u : MassGap.SUN.SU N) :
    ((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
      = Matrix.conjTranspose (u : Matrix (Fin N) (Fin N) ℂ) := by
  have hu : (u : Matrix (Fin N) (Fin N) ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp u.2).1
  have h1 : Matrix.conjTranspose (u : Matrix (Fin N) (Fin N) ℂ)
      * (u : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hu
    rwa [Matrix.star_eq_conjTranspose] at this
  have h2 : ((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
      * (u : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    exact Submonoid.coe_one _
  have h3 : (u : Matrix (Fin N) (Fin N) ℂ)
      * Matrix.conjTranspose (u : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hu
    rwa [Matrix.star_eq_conjTranspose] at this
  calc ((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
      = ((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) * 1 := by rw [Matrix.mul_one]
    _ = ((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
          * ((u : Matrix (Fin N) (Fin N) ℂ)
            * Matrix.conjTranspose (u : Matrix (Fin N) (Fin N) ℂ)) := by rw [h3]
    _ = (((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
          * (u : Matrix (Fin N) (Fin N) ℂ))
          * Matrix.conjTranspose (u : Matrix (Fin N) (Fin N) ℂ) := by rw [Matrix.mul_assoc]
    _ = Matrix.conjTranspose (u : Matrix (Fin N) (Fin N) ℂ) := by rw [h2, Matrix.one_mul]

/-- **`Re tr` does not see inversion on `SU(N)`**: the inverse is the conjugate transpose, whose
trace is the conjugate of the trace, and conjugation fixes the real part. -/
theorem re_trace_inv (u : MassGap.SUN.SU N) :
    (Matrix.trace ((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re
      = (Matrix.trace ((u : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re := by
  rw [coe_inv_eq_conjTranspose, Matrix.trace_conjTranspose]
  simp

/-- **THE TWO ORDERINGS OF ONE PLANE CARRY THE SAME WILSON DENSITY.** This is what makes the ordered
plaquette type a double count rather than a different theory: both copies of a geometric plaquette
contribute the same energy. -/
theorem wilsonDensity_hol_swap (μ ν : Fin d) (x : Site d n)
    (U : Link d n → MassGap.SUN.SU N) :
    wilsonDensity (wilsonHol (bd (d := d) (n := n)) (((ν, μ), x) : Plaq d n) U)
      = wilsonDensity (wilsonHol (bd (d := d) (n := n)) (((μ, ν), x) : Plaq d n) U) := by
  rw [hol_swap]
  unfold wilsonDensity
  rw [re_trace_inv]

/-- **A degenerate pair costs nothing**, so the diagonal of the plaquette type is inert in the sum. -/
theorem wilsonDensity_hol_diag (hN : N ≠ 0) (μ : Fin d) (x : Site d n)
    (U : Link d n → MassGap.SUN.SU N) :
    wilsonDensity (wilsonHol (bd (d := d) (n := n)) (((μ, μ), x) : Plaq d n) U) = 0 := by
  rw [hol_diag]
  exact wilsonDensity_one hN

/-! ### The double count, as a statement about sums -/

/-- **A symmetric function vanishing on the diagonal sums over ORDERED pairs to twice its sum over
`μ < ν`.** Pure `Finset` combinatorics: the `¬(a < b)` half is the `b < a` half plus a diagonal that
contributes nothing, and `Prod.swap` is a bijection from `{a < b}` onto `{b < a}`. -/
theorem sum_pair_eq_two_mul_lt {d : ℕ} (g : Fin d × Fin d → ℝ)
    (hsymm : ∀ p : Fin d × Fin d, g p.swap = g p)
    (hdiag : ∀ a : Fin d, g (a, a) = 0) :
    ∑ p : Fin d × Fin d, g p
      = 2 * ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2), g p := by
  classical
  have hTS : ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.2 < p.1), g p
      = ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2), g p := by
    have himg : (Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2)).image Prod.swap
        = Finset.univ.filter (fun p : Fin d × Fin d => p.2 < p.1) := by
      ext p
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact hq
      · intro hp
        exact ⟨p.swap, hp, Prod.swap_swap p⟩
    have hinj : ∀ a ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2),
        ∀ b ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2),
        Prod.swap a = Prod.swap b → a = b := by
      intro a _ b _ h
      simpa using congrArg Prod.swap h
    rw [← himg, Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun p _ => hsymm p)
  have hnot : ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => ¬ p.1 < p.2), g p
      = ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.2 < p.1), g p := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact not_lt.mpr (le_of_lt hp)
    · intro p hp hpT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hpT
      obtain ⟨a, b⟩ := p
      have hab : a = b := le_antisymm (not_lt.mp hpT) (not_lt.mp hp)
      subst hab
      exact hdiag a
  have hsplit : ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2), g p
      + ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => ¬ p.1 < p.2), g p
      = ∑ p : Fin d × Fin d, g p :=
    Finset.sum_filter_add_sum_filter_not Finset.univ _ g
  rw [← hsplit, hnot, hTS]
  ring

/-- **THE ORDERED PLAQUETTE TYPE DOUBLE-COUNTS EVERY PLANE.** The Wilson action density summed over
`Plaq d n` — which is what `System.action` sums, since `Finset.univ` ranges over the whole type — is
exactly twice the sum over the planes with `μ < ν`, the range the standard Wilson action uses. -/
theorem plaq_ordered_double_counts (hN : N ≠ 0) (U : Link d n → MassGap.SUN.SU N) :
    ∑ q : Plaq d n, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)
      = 2 * ∑ q ∈ Finset.univ.filter (fun q : Plaq d n => q.1.1 < q.1.2),
          wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) := by
  classical
  have hfil : Finset.univ.filter (fun q : Plaq d n => q.1.1 < q.1.2)
      = (Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2))
        ×ˢ (Finset.univ : Finset (Site d n)) := by
    ext q
    simp [Finset.mem_filter, Finset.mem_product]
  rw [hfil, Finset.sum_product, Fintype.sum_prod_type]
  exact sum_pair_eq_two_mul_lt
    (fun p => ∑ x : Site d n, wilsonDensity (wilsonHol (bd (d := d) (n := n)) (p, x) U))
    (fun p => Finset.sum_congr rfl (fun x _ => wilsonDensity_hol_swap p.1 p.2 x U))
    (fun a => Finset.sum_eq_zero (fun x _ => wilsonDensity_hol_diag hN a x U))

/-- The system's action is the sum of the density over the ordered plaquette type. -/
theorem sysWilson_action (U : Link d n → MassGap.SUN.SU N) :
    (sysWilson N d n).action U
      = ∑ q : Plaq d n, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) := rfl

/-- **The action at the Lean normalisation is twice the standard Wilson action.** -/
theorem sysWilson_action_eq_two_mul (hN : N ≠ 0) (U : Link d n → MassGap.SUN.SU N) :
    (sysWilson N d n).action U
      = 2 * ∑ q ∈ Finset.univ.filter (fun q : Plaq d n => q.1.1 < q.1.2),
          wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) := by
  rw [sysWilson_action, plaq_ordered_double_counts hN U]

/-- **`β_lean = β_std / 2`, AS A THEOREM.** The Boltzmann weight this system carries at coupling `β`
is the STANDARD Wilson weight — the one summing each plane once — at coupling `2β`. So a number
quoted against a source using the standard normalisation is `2β` where this tree writes `β`. -/
theorem boltz_eq_std (hN : N ≠ 0) (β : ℝ) (U : Link d n → MassGap.SUN.SU N) :
    (sysWilson N d n).boltz β U
      = Real.exp (-(2 * β) * ∑ q ∈ Finset.univ.filter (fun q : Plaq d n => q.1.1 < q.1.2),
          wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)) := by
  unfold System.boltz
  rw [sysWilson_action_eq_two_mul hN U]
  congr 1
  ring

#print axioms hol_word
#print axioms hol_swap
#print axioms hol_diag
#print axioms coe_inv_eq_conjTranspose
#print axioms re_trace_inv
#print axioms wilsonDensity_hol_swap
#print axioms wilsonDensity_hol_diag
#print axioms sum_pair_eq_two_mul_lt
#print axioms plaq_ordered_double_counts
#print axioms sysWilson_action
#print axioms sysWilson_action_eq_two_mul
#print axioms boltz_eq_std

end MassGap.PlaqCount
