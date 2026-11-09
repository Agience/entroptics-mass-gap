import Mathlib
import MassGap.TomboulisYaffe
import MassGap.VortexStrong

/-!
# MassGap.Chessboard — reflection positivity on the rectangular `SU(2)` torus and the Schwarz doubling

`TomboulisYaffe.ChessboardFlux L a b o β` asks, on every `AdmTwo` rectangle, for
`⟨F[s] W(C)⟩ ≤ ⟨F[s]⟩^{mn/(L_a L_b)}` with `s = sIn` and `s = sOut`. This module proves reflection
positivity of the Wilson measure on `RectWilson.RSite L`, one Schwarz doubling of the rectangle at the
real objects (`ev`, `fluxOp`, `wObs`, `sIn`, `rectWord`), its iteration along `a` and along `b`, and from
these the hypothesis-free chain `chain_full` from an admissible rectangle to the loop once around the
whole `(b, a)` torus. The inside half of `ChessboardFlux` follows from `chain_full` and one further
input, `FullLoopFlux`, which is not known to hold and fails in some geometries.

## Sources

* Kanazawa, arXiv:0808.3442, proof of Theorem 2, eqs. (34)–(41) and Fig. 2 (site reflections only).
* Tomboulis and Yaffe, Commun. Math. Phys. 100 (1985) 313.

## What is proved

1. **The site reflection** in direction `a` about `x_a = P` (`L_a = 2h`): sites `rs`, links `rl`
   (`a`-links reversed, `σi` inverts them), plaquettes `rp`; `Θ` is the configuration map, an
   involution (`Θ_Θ`) preserving the product Haar measure (`Θ_mp`). `wd_refl`: against a central
   self-inverse `z`, `wd(z U_q(ΘU)) = wd(z U_{rp q}(U))`.
2. **The split** (`action_split`): `S = S_left + S_left ∘ Θ + S_planes`, with `Sset`, `Tset`, `Rset` the
   left half, the right half and the two fixed planes `x_a = P`, `x_a = P + h`; the left action reads
   `Sset ∪ Rset` (`Aact_reads`), the plane action reads `Rset` (`Cact_reads`).
3. **Reflection positivity** (`rp_nonneg`), at every real `β`: `∫ G (G ∘ Θ) e^{−βS} ≥ 0` for continuous
   `G` reading `Sset ∪ Rset`, from `ActionSplit.pairing_nonneg_of_local`. `bil_symm` and the
   **Cauchy–Schwarz inequality** `bil_sq_le`: `⟨G, H⟩_Θ² ≤ ⟨G, G⟩_Θ ⟨H, H⟩_Θ`.
4. **Flux operators** (`int_flux_wObs`, `int_flux2_wObs`, `fluxOp_Θ`, `sheet_rp`, `vortexOp_reads`):
   a sheet reflects to the sheet at `2P − 1 − p_a`; two flux operators of disjoint sheets integrate to
   `(WN(1) − WN(ζ₁) − WN(ζ₂) + WN(ζ₁ζ₂))/4`; with `count_zero` and `WN_step_mul` this is the projection
   identity `⟨F[V] F[V^Θ] W⟩ = ⟨F[V] W⟩` used in the doubling.
5. **One doubling** (`doubling`): for `a ≠ b`, `L_a = 2h`, `0 < m ≤ h`,
   `⟨F[sIn] W(m × n)⟩² ≤ ⟨F[sIn] W(2m × n)⟩` and the right side is `≥ 0`. The trace is written through
   the eight real coordinates `Xg` (`sumX`: `Σ_k X_k(A) X_k(B) = 2(1 − wd(A B⁻¹))`), the right side of
   the rectangle lies in the plane, and the reflected left part closes the doubled rectangle
   (`pathA_Θ`, `pathB_Θ`, `rectHol_eq`).
6. **Iteration** (`WN_move`, `ev_move`, `chain_a`, `turn`): the sheet slides inside the rectangle
   without changing `⟨F W⟩`; `|⟨F[sIn] W(m × n)⟩|^{2^p} ≤ ⟨F[sIn] W(L_a × n)⟩` for `L_a = 2^p m`; the
   full-width rectangle turns to the `(b, a)` orientation.
7. **The chain** (`chain_full`), with no hypothesis beyond admissibility: for `L_a = 2^p m`,
   `L_b = 2^q n`, `|⟨F[sIn] W(m × n)⟩|^{2^{p+q}} ≤ ⟨F[sIn_{(b,a)}] W(L_b × L_a)⟩`, the right side the
   loop with holonomy `P_b P_a P_b⁻¹ P_a⁻¹`. **The sign form of the input** (`fullLoopFlux_iff`, via
   `ev_fluxOp_wObs_split`): `FullLoopFlux L a b o β ↔ 0 ≤ ⟨F[sIn_{(b,a)}] · wd(P_b P_a P_b⁻¹ P_a⁻¹)⟩`.
   **Conditional results**: `chessboard_in` gives, from `FullLoopFlux`, on every `AdmTwo` rectangle
   `⟨F[sIn] W(C)⟩ ≤ ⟨F[sIn]⟩^{mn/(L_a L_b)}`; `chessboardFlux_of` gives `ChessboardFlux` from
   `FullLoopFlux` and `OutsideFlux`. Neither input is proved.

## What is not proved

* `FullLoopFlux L a b o β`: `⟨F[sIn_{(b,a)}] W(L_b × L_a)⟩ ≤ (1 − zR)/2`, the flux operator times the
  Wilson observable of the loop once around the whole `(b, a)` torus (holonomy
  `P_b P_a P_b⁻¹ P_a⁻¹`, the commutator of the two Polyakov lines at `o`). After `p + q` doublings
  this loop is what the chain ends at; it is not the identity on the lattice. Equivalently
  (`fullLoopFlux_iff`) `0 ≤ ⟨F · wd(P_b P_a P_b⁻¹ P_a⁻¹)⟩`; `fluxOp` is not pointwise `≥ 0`. This
  input is not known to hold and fails in some geometries: in the exact two-dimensional analogue
  `Z · ⟨F · wd(W_full)⟩ = −Σ_{j half-integer} c_j^N/(d_j² − 1) < 0` at every `β ≠ 0`; in four
  dimensions the leading small-`β` term is `u^N (9K − 13)/12` with `K = L_c L_d`, negative for
  `K = 1` (e.g. `L = (2, 2, 1, 1)`, `N` even), so `FullLoopFlux` is false there at small `β > 0`. That
  four-dimensional statement is a leading-order computation, not machine-checked. For `K ≥ 2` it is
  open. This is the gap in Kanazawa eq. (40), where "the rectangle finally vanishes away" sets the
  full-torus loop to `1`.
* `OutsideFlux L a b o β`: the `sOut` half of `ChessboardFlux`, as stated there. No proof is known.

No `sorry`, no new axiom; `PlaqVariance.wilson_reflection_positive_input` is not used.

DERIVED (module-wide): `2` is `L_a/h` (the two halves of a periodic site reflection), the `2` of
`2m` (one doubling) and of `2^p`, and `|ℤ₂|`; `8 = 2 · 2 · 2` real coordinates of a `2 × 2` complex
matrix; `1` the unit step of a sheet.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.Chessboard

open MeasureTheory MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.GapSideVortexRect
  MassGap.TomboulisYaffe MassGap.ActionSplit
open MassGap.MovedTorusDecimation (val_finRotate integrable_of_continuous)

local notation "wd" => WilsonAction.wilsonDensity

/-! ## 1. A nonnegative quadratic polynomial -/

theorem sq_le_of_quad {A B C : ℝ} (h : ∀ t : ℝ, 0 ≤ A + 2 * t * B + t ^ 2 * C) :
    B ^ 2 ≤ A * C := by
  have hd := discrim_le_zero (K := ℝ) (a := C) (b := 2 * B) (c := A) (fun t => by
    have := h t; nlinarith [this])
  unfold discrim at hd
  nlinarith [hd]

/-! ## 2. The site reflection in direction `a` about the plane `x_a = P` -/

section Refl

variable (L : Fin 4 → ℕ) (a : Fin 4) [NeZero (L a)] (P : Fin (L a))

theorem finRotate_eq_add_one {n : ℕ} [NeZero n] (v : Fin n) : finRotate n v = v + 1 := by
  apply Fin.ext
  rw [val_finRotate, Fin.val_add, Fin.val_one', Nat.add_mod_mod]

/-- The mirror image of a site in the plane `x_a = P`: `x_a ↦ 2P − x_a`. -/
def rs (x : RSite L) : RSite L := Function.update x a (P + P - x a)

omit [NeZero (L a)] in
theorem rs_self (x : RSite L) : rs L a P x a = P + P - x a := Function.update_self _ _ _

omit [NeZero (L a)] in
theorem rs_ne {c : Fin 4} (h : c ≠ a) (x : RSite L) : rs L a P x c = x c :=
  Function.update_of_ne h _ _

theorem rshift_self (x : RSite L) : rshift L a x a = x a + 1 := by
  rw [rshift_self' L a x, finRotate_eq_add_one]

theorem rs_rs (x : RSite L) : rs L a P (rs L a P x) = x := by
  funext c
  by_cases hc : c = a
  · subst hc; rw [rs_self, rs_self]; abel
  · rw [rs_ne L a P hc, rs_ne L a P hc]

theorem rshift_comm' {i j : Fin 4} (h : i ≠ j) (x : RSite L) :
    rshift L i (rshift L j x) = rshift L j (rshift L i x) := by
  funext c
  by_cases hci : c = i
  · subst hci
    simp only [rshift_self', rshift_ne' L h]
  · by_cases hcj : c = j
    · subst hcj
      simp only [rshift_self', rshift_ne' L hci]
    · simp only [rshift_ne' L hci, rshift_ne' L hcj]

theorem rs_rshift {j : Fin 4} (hj : j ≠ a) (x : RSite L) :
    rs L a P (rshift L j x) = rshift L j (rs L a P x) := by
  funext c
  by_cases hca : c = a
  · subst hca
    rw [rs_self, rshift_ne' L (Ne.symm hj), rshift_ne' L (Ne.symm hj), rs_self]
  · by_cases hcj : c = j
    · subst hcj
      rw [rs_ne L a P hca, rshift_self', rshift_self', rs_ne L a P hca]
    · rw [rs_ne L a P hca, rshift_ne' L hcj, rshift_ne' L hcj, rs_ne L a P hca]

theorem rs_shift_a (x : RSite L) : rshift L a (rs L a P (rshift L a x)) = rs L a P x := by
  funext c
  by_cases hca : c = a
  · subst hca
    rw [rshift_self, rs_self, rshift_self, rs_self]
    abel
  · rw [rshift_ne' L hca, rs_ne L a P hca, rshift_ne' L hca, rs_ne L a P hca]

theorem rs_rs_shift (x : RSite L) : rs L a P (rshift L a (rs L a P (rshift L a x))) = x := by
  rw [rs_shift_a, rs_rs]

/-- The mirror image of a link: an `a`-link leaving `x` goes to the `a`-link entering `2P − x_a`,
that is the one leaving `rs (x + e_a)`; every other link goes to the link at the mirrored site. -/
def rl (l : RLink L) : RLink L :=
  if l.1 = a then (a, rs L a P (rshift L a l.2)) else (l.1, rs L a P l.2)

theorem rl_invol : Function.Involutive (rl L a P) := by
  intro l
  obtain ⟨i, x⟩ := l
  by_cases h : i = a
  · subst h
    simp [rl, rs_rs_shift]
  · simp [rl, h, rs_rs]

/-- The link permutation of the reflection. -/
def θp : Equiv.Perm (RLink L) := Function.Involutive.toPerm _ (rl_invol L a P)

/-- The coordinate map: inversion on `a`-links (their orientation is reversed), identity otherwise. -/
def σi (l : RLink L) : SUN.SU 2 → SUN.SU 2 := if l.1 = a then fun g => g⁻¹ else id

/-- **The reflection of a configuration.** -/
def Θ (U : RLink L → SUN.SU 2) : RLink L → SUN.SU 2 := twist (θp L a P) (σi L a) U

theorem Θ_a (U : RLink L → SUN.SU 2) (y : RSite L) :
    Θ L a P U (a, y) = (U (a, rs L a P (rshift L a y)))⁻¹ := by
  simp [Θ, twist, θp, σi, rl]

theorem Θ_ne {i : Fin 4} (h : i ≠ a) (U : RLink L → SUN.SU 2) (y : RSite L) :
    Θ L a P U (i, y) = U (i, rs L a P y) := by
  simp [Θ, twist, θp, σi, rl, h]

theorem Θ_Θ (U : RLink L → SUN.SU 2) : Θ L a P (Θ L a P U) = U := by
  funext l
  obtain ⟨i, y⟩ := l
  by_cases h : i = a
  · subst h
    rw [Θ_a, Θ_a, rs_rs_shift, inv_inv]
  · rw [Θ_ne L a P h, Θ_ne L a P h, rs_rs]

theorem continuous_Θ : Continuous (Θ L a P) := by
  refine continuous_pi fun l => ?_
  show Continuous fun U : RLink L → SUN.SU 2 => σi L a l (U (θp L a P l))
  unfold σi
  split_ifs
  · exact (continuous_apply _).inv
  · exact continuous_apply _

omit [NeZero (L a)] in
theorem σi_mp (l : RLink L) :
    MeasurePreserving (σi L a l) (probHaar (SUN.SU 2)) (probHaar (SUN.SU 2)) := by
  unfold σi
  split_ifs
  · exact Measure.measurePreserving_inv (probHaar (SUN.SU 2))
  · exact MeasurePreserving.id _

theorem Θ_mp : MeasurePreserving (Θ L a P) (Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))
    (Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)) :=
  twist_measurePreserving (probHaar (SUN.SU 2)) (θp L a P) (σi L a) (σi_mp L a)

/-- The mirror image of a plaquette. -/
def rp (q : RPlaq L) : RPlaq L :=
  if q.1.1 = a ∨ q.1.2 = a then (q.1, rs L a P (rshift L a q.2)) else (q.1, rs L a P q.2)

theorem rp_invol : Function.Involutive (rp L a P) := by
  intro q
  obtain ⟨⟨i, j⟩, x⟩ := q
  by_cases h : i = a ∨ j = a
  · simp only [rp, h, if_true, rs_rs_shift]
  · simp only [rp, h, if_false, rs_rs]

/-- The plaquette permutation of the reflection. -/
def ρp : Equiv.Perm (RPlaq L) := Function.Involutive.toPerm _ (rp_invol L a P)

/-- A degenerate plaquette has trivial holonomy. An alias of `VortexStrong.rhol_diag`. -/
alias rhol_diag' := MassGap.VortexStrong.rhol_diag

theorem wd_central (z g : SUN.SU 2) (hz : ∀ k, z * k = k * z) (hzi : z⁻¹ = z) (h : SUN.SU 2) :
    wd (z * (g * h⁻¹ * g⁻¹)) = wd (z * h) := by
  have e : z * (g * h⁻¹ * g⁻¹) = g * (z * h⁻¹) * g⁻¹ := by
    rw [← mul_assoc, ← mul_assoc, hz g, mul_assoc g z]
  rw [e, WilsonAction.wilsonDensity_conj, ← wilsonDensity_inv, mul_inv_rev, inv_inv, hzi, hz h]

/-- **A reflected plaquette holonomy** is conjugate to the mirrored plaquette holonomy or to its
inverse; against a central `z` with `z⁻¹ = z` the Wilson density cannot tell them apart. -/
theorem wd_refl (z : SUN.SU 2) (hz : ∀ k, z * k = k * z) (hzi : z⁻¹ = z) (q : RPlaq L)
    (U : RLink L → SUN.SU 2) :
    wd (z * rhol L q (Θ L a P U)) = wd (z * rhol L (rp L a P q) U) := by
  obtain ⟨⟨i, j⟩, x⟩ := q
  by_cases hij : i = j
  · subst hij
    unfold rp
    split_ifs <;> simp only [rhol_diag']
  by_cases hia : i = a
  · subst hia
    have hja : j ≠ i := Ne.symm hij
    have hr : rp L i P ((i, j), x) = ((i, j), rs L i P (rshift L i x)) := by simp [rp]
    rw [hr]
    set y := rs L i P (rshift L i x) with hy
    have e1 : rs L i P (rshift L i (rshift L j x)) = rshift L j y := by
      rw [rshift_comm' L hij, rs_rshift L i P hja]
    have e2 : rs L i P x = rshift L i y := by rw [hy, rs_shift_a]
    have hh : rhol L ((i, j), x) (Θ L i P U)
        = (U (i, y))⁻¹ * (rhol L ((i, j), y) U)⁻¹ * ((U (i, y))⁻¹)⁻¹ := by
      simp only [rhol, Θ_a, Θ_ne L i P hja, e1, e2, ← hy]
      group
    rw [hh, wd_central _ _ hz hzi]
  by_cases hja : j = a
  · subst hja
    have hr : rp L j P ((i, j), x) = ((i, j), rs L j P (rshift L j x)) := by simp [rp]
    rw [hr]
    set y := rs L j P (rshift L j x) with hy
    have e1 : rs L j P (rshift L j (rshift L i x)) = rshift L i y := by
      rw [rshift_comm' L (Ne.symm hij), rs_rshift L j P hia]
    have e2 : rs L j P x = rshift L j y := by rw [hy, rs_shift_a]
    have hh : rhol L ((i, j), x) (Θ L j P U)
        = (U (j, y))⁻¹ * (rhol L ((i, j), y) U)⁻¹ * ((U (j, y))⁻¹)⁻¹ := by
      simp only [rhol, Θ_a, Θ_ne L j P hia, e1, e2, ← hy]
      group
    rw [hh, wd_central _ _ hz hzi]
  · have hr : rp L a P ((i, j), x) = ((i, j), rs L a P x) := by simp [rp, hia, hja]
    rw [hr]
    simp only [rhol, Θ_ne L a P hia, Θ_ne L a P hja, rs_rshift L a P hia, rs_rshift L a P hja]

theorem wd_refl_one (q : RPlaq L) (U : RLink L → SUN.SU 2) :
    wd (rhol L q (Θ L a P U)) = wd (rhol L (rp L a P q) U) := by
  have := wd_refl L a P 1 (fun k => by rw [one_mul, mul_one]) inv_one q U
  simpa only [one_mul] using this

/-- The Wilson weight of the rectangular torus. -/
def E (β : ℝ) (U : RLink L → SUN.SU 2) : ℝ := Real.exp (-β * ∑ q, wd (rhol L q U))

theorem continuous_E (β : ℝ) : Continuous (E L β) := by
  have := continuous_integrand L β (fun _ => 1)
  simp only [one_mul] at this
  exact this

theorem E_Θ (β : ℝ) (U : RLink L → SUN.SU 2) : E L β (Θ L a P U) = E L β U := by
  have hs : ∑ q, wd (rhol L q (Θ L a P U)) = ∑ q, wd (rhol L q U) := by
    rw [Finset.sum_congr rfl fun q _ => wd_refl_one L a P q U]
    exact Equiv.sum_comp (ρp L a P) (fun q => wd (rhol L q U))
  unfold E
  rw [hs]

/-! ## 3. The two halves and the plane -/

/-- The distance of an `a`-coordinate from the plane, read forward: `(v − P) mod L_a`. -/
def dd (v : Fin (L a)) : ℕ := (v - P).val

omit [NeZero (L a)] in
theorem dd_lt (v : Fin (L a)) : dd L a P v < L a := (v - P).isLt

theorem dd_refl (v : Fin (L a)) : dd L a P (P + P - v) = (L a - dd L a P v) % L a := by
  unfold dd
  rw [show P + P - v - P = -(v - P) by abel, Fin.val_neg']

theorem dd_succ (v : Fin (L a)) : dd L a P (v + 1) = (dd L a P v + 1) % L a := by
  unfold dd
  rw [show v + 1 - P = (v - P) + 1 by abel, Fin.val_add, Fin.val_one', Nat.add_mod_mod]

theorem dd_refl_succ (v : Fin (L a)) : dd L a P (P + P - (v + 1)) = L a - 1 - dd L a P v := by
  rw [dd_refl, dd_succ]
  have := dd_lt L a P v
  by_cases hc : dd L a P v + 1 = L a
  · rw [hc, Nat.mod_self, Nat.sub_zero, Nat.mod_self]; omega
  · rw [Nat.mod_eq_of_lt (by omega : dd L a P v + 1 < L a), Nat.mod_eq_of_lt (by omega)]; omega

theorem rco_fix (h : ℕ) (hL : L a = 2 * h) (v : Fin (L a)) (hv : dd L a P v = 0 ∨ dd L a P v = h) :
    P + P - v = v := by
  have he : (v - P) + (v - P) = 0 := by
    apply Fin.ext
    rw [Fin.val_add, Fin.val_zero]
    unfold dd at hv
    rcases hv with hv | hv
    · rw [hv]; simp
    · rw [hv, ← two_mul, ← hL, Nat.mod_self]
  calc P + P - v = v - ((v - P) + (v - P)) := by abel
    _ = v := by rw [he, sub_zero]

theorem rs_fix (h : ℕ) (hL : L a = 2 * h) (x : RSite L)
    (hv : dd L a P (x a) = 0 ∨ dd L a P (x a) = h) : rs L a P x = x := by
  unfold rs
  rw [rco_fix L a P h hL _ hv, Function.update_eq_self]

variable (h : ℕ)

/-- The left half: `a`-links at distance `≥ h`, other links at distance `> h`. -/
def Sset : Finset (RLink L) := Finset.univ.filter fun l =>
  (l.1 = a ∧ h ≤ dd L a P (l.2 a)) ∨ (l.1 ≠ a ∧ h < dd L a P (l.2 a))

/-- The right half. -/
def Tset : Finset (RLink L) := Finset.univ.filter fun l =>
  (l.1 = a ∧ dd L a P (l.2 a) < h) ∨ (l.1 ≠ a ∧ 0 < dd L a P (l.2 a) ∧ dd L a P (l.2 a) < h)

/-- The two fixed planes `x_a = P` and `x_a = P + h`: the non-`a` links there. -/
def Rset : Finset (RLink L) := Finset.univ.filter fun l =>
  l.1 ≠ a ∧ (dd L a P (l.2 a) = 0 ∨ dd L a P (l.2 a) = h)

/-- A plaquette of the left half. -/
def plL (q : RPlaq L) : Prop :=
  q.1.1 ≠ q.1.2 ∧ (((q.1.1 = a ∨ q.1.2 = a) ∧ h ≤ dd L a P (q.2 a)) ∨
    (q.1.1 ≠ a ∧ q.1.2 ≠ a ∧ h < dd L a P (q.2 a)))

instance (q : RPlaq L) : Decidable (plL L a P h q) := by unfold plL; infer_instance

omit [NeZero (L a)] in
theorem disj_ST : Disjoint (Sset L a P h) (Tset L a P h) := by
  rw [Finset.disjoint_left]
  intro l h1 h2
  simp only [Sset, Tset, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  omega

omit [NeZero (L a)] in
theorem disj_SR : Disjoint (Sset L a P h) (Rset L a P h) := by
  rw [Finset.disjoint_left]
  intro l h1 h2
  simp only [Sset, Rset, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  omega

omit [NeZero (L a)] in
theorem disj_TR : Disjoint (Tset L a P h) (Rset L a P h) := by
  rw [Finset.disjoint_left]
  intro l h1 h2
  simp only [Tset, Rset, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  omega

theorem θp_apply (l : RLink L) : θp L a P l = rl L a P l := rfl

theorem θ_fix_R (hL : L a = 2 * h) (l : RLink L) (hl : l ∈ Rset L a P h) : θp L a P l = l := by
  simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  obtain ⟨i, x⟩ := l
  rw [θp_apply]
  simp only [rl, hl.1, if_false]
  rw [rs_fix L a P h hL x hl.2]

omit [NeZero (L a)] in
theorem σ_fix_R (l : RLink L) (hl : l ∈ Rset L a P h) (u : SUN.SU 2) : σi L a l u = u := by
  simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  simp [σi, hl.1]

theorem θ_S_T (hL : L a = 2 * h) (l : RLink L) (hl : l ∈ Sset L a P h) :
    θp L a P l ∈ Tset L a P h := by
  simp only [Sset, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  obtain ⟨i, x⟩ := l
  rw [θp_apply]
  simp only [Tset, Finset.mem_filter, Finset.mem_univ, true_and]
  have hlt := dd_lt L a P (x a)
  by_cases hi : i = a
  · subst hi
    simp only [rl, if_true, rs_self, rshift_self, dd_refl_succ]
    simp only [true_and, ne_eq, not_true_eq_false, false_and, or_false] at hl ⊢
    omega
  · simp only [rl, hi, if_false, rs_self, dd_refl]
    simp only [hi, false_and, false_or, ne_eq, not_false_eq_true, true_and] at hl ⊢
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

omit [NeZero (L a)] in
theorem memSR_a (y : RSite L) (hy : h ≤ dd L a P (y a)) : (a, y) ∈ Sset L a P h ∪ Rset L a P h := by
  simp [Sset, hy]

omit [NeZero (L a)] in
theorem memSR_ne {i : Fin 4} (hi : i ≠ a) (y : RSite L)
    (hy : h ≤ dd L a P (y a) ∨ dd L a P (y a) = 0) : (i, y) ∈ Sset L a P h ∪ Rset L a P h := by
  simp only [Sset, Rset, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, hi,
    false_and, false_or, ne_eq, not_false_eq_true]
  omega

omit [NeZero (L a)] in
theorem memR_ne {i : Fin 4} (hi : i ≠ a) (y : RSite L)
    (hy : dd L a P (y a) = 0 ∨ dd L a P (y a) = h) : (i, y) ∈ Rset L a P h := by
  simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hi, hy⟩

theorem dd_shift_a (hL : L a = 2 * h) (x : RSite L) (hx : h ≤ dd L a P (x a)) :
    h ≤ dd L a P (rshift L a x a) ∨ dd L a P (rshift L a x a) = 0 := by
  rw [rshift_self, dd_succ]
  have := dd_lt L a P (x a)
  by_cases hc : dd L a P (x a) + 1 = L a
  · right; rw [hc, Nat.mod_self]
  · left; rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- **A left plaquette reads the left half and the planes only.** -/
theorem plL_reads (hL : L a = 2 * h) (q : RPlaq L) (hq : plL L a P h q) (U V : RLink L → SUN.SU 2)
    (hUV : ∀ l ∈ Sset L a P h ∪ Rset L a P h, U l = V l) : rhol L q U = rhol L q V := by
  obtain ⟨⟨i, j⟩, x⟩ := q
  obtain ⟨hij, hq⟩ := hq
  simp only at hij hq
  have key : (i, x) ∈ Sset L a P h ∪ Rset L a P h ∧ (j, rshift L i x) ∈ Sset L a P h ∪ Rset L a P h ∧
      (i, rshift L j x) ∈ Sset L a P h ∪ Rset L a P h ∧ (j, x) ∈ Sset L a P h ∪ Rset L a P h := by
    rcases hq with ⟨hm, hc⟩ | ⟨hia, hja, hc⟩
    · rcases hm with hia | hja
      · subst hia
        have hja : j ≠ i := Ne.symm hij
        refine ⟨memSR_a L i P h x hc, memSR_ne L i P h hja _ (dd_shift_a L i P h hL x hc),
          memSR_a L i P h _ (by rw [rshift_ne' L (Ne.symm hja)]; exact hc),
          memSR_ne L i P h hja _ (Or.inl hc)⟩
      · subst hja
        have hia : i ≠ j := hij
        refine ⟨memSR_ne L j P h hia _ (Or.inl hc), memSR_a L j P h _ (by rw [rshift_ne' L (Ne.symm hia)]; exact hc),
          memSR_ne L j P h hia _ (dd_shift_a L j P h hL x hc), memSR_a L j P h x hc⟩
    · refine ⟨memSR_ne L a P h hia _ (Or.inl hc.le), memSR_ne L a P h hja _ ?_,
        memSR_ne L a P h hia _ ?_, memSR_ne L a P h hja _ (Or.inl hc.le)⟩
      · rw [rshift_ne' L (Ne.symm hia)]; exact Or.inl hc.le
      · rw [rshift_ne' L (Ne.symm hja)]; exact Or.inl hc.le
  obtain ⟨k1, k2, k3, k4⟩ := key
  simp only [rhol]
  rw [hUV _ k1, hUV _ k2, hUV _ k3, hUV _ k4]

theorem dd_rp_mixed (q : RPlaq L) (hm : q.1.1 = a ∨ q.1.2 = a) :
    dd L a P ((rp L a P q).2 a) = L a - 1 - dd L a P (q.2 a) := by
  simp only [rp, hm, if_true, rs_self, rshift_self, dd_refl_succ]

theorem dd_rp_tr (q : RPlaq L) (hm : ¬ (q.1.1 = a ∨ q.1.2 = a)) :
    dd L a P ((rp L a P q).2 a) = (L a - dd L a P (q.2 a)) % L a := by
  simp only [rp, hm, if_false, rs_self, dd_refl]

omit [NeZero (L a)] in
theorem rp_fst (q : RPlaq L) : (rp L a P q).1 = q.1 := by
  unfold rp; split_ifs <;> rfl

/-- **No plaquette lies in both halves.** -/
theorem not_plL_both (hL : L a = 2 * h) (q : RPlaq L) :
    ¬ (plL L a P h q ∧ plL L a P h (rp L a P q)) := by
  rintro ⟨⟨hij, h1⟩, ⟨-, h2⟩⟩
  rw [rp_fst] at h2
  have hlt := dd_lt L a P (q.2 a)
  by_cases hm : q.1.1 = a ∨ q.1.2 = a
  · rw [dd_rp_mixed L a P q hm] at h2
    have hm' : ¬ (q.1.1 ≠ a ∧ q.1.2 ≠ a) := by tauto
    have h1' : h ≤ dd L a P (q.2 a) := by tauto
    have h2' : h ≤ L a - 1 - dd L a P (q.2 a) := by tauto
    omega
  · rw [dd_rp_tr L a P q hm] at h2
    have h1' : h < dd L a P (q.2 a) := by tauto
    have h2' : h < (L a - dd L a P (q.2 a)) % L a := by tauto
    rw [Nat.mod_eq_of_lt (by omega)] at h2'
    omega

/-- **A plaquette in neither half lies in a fixed plane**: it reads the planes only. -/
theorem rest_reads (hL : L a = 2 * h) (q : RPlaq L) (hd : q.1.1 ≠ q.1.2) (h1 : ¬ plL L a P h q)
    (h2 : ¬ plL L a P h (rp L a P q)) (U V : RLink L → SUN.SU 2)
    (hUV : ∀ l ∈ Rset L a P h, U l = V l) : rhol L q U = rhol L q V := by
  obtain ⟨⟨i, j⟩, x⟩ := q
  have hlt := dd_lt L a P (x a)
  by_cases hm : i = a ∨ j = a
  · exfalso
    apply h2
    refine ⟨by rw [rp_fst]; exact hd, Or.inl ⟨by rw [rp_fst]; exact hm, ?_⟩⟩
    rw [dd_rp_mixed L a P _ hm]
    have : ¬ h ≤ dd L a P (x a) := fun hc => h1 ⟨hd, Or.inl ⟨hm, hc⟩⟩
    simp only at this ⊢
    omega
  · have hia : i ≠ a := fun e => hm (Or.inl e)
    have hja : j ≠ a := fun e => hm (Or.inr e)
    have c1 : ¬ h < dd L a P (x a) := fun hc => h1 ⟨hd, Or.inr ⟨hia, hja, hc⟩⟩
    have c2 : ¬ h < (L a - dd L a P (x a)) % L a := by
      intro hc
      apply h2
      refine ⟨by rw [rp_fst]; exact hd, Or.inr ⟨by rw [rp_fst]; exact hia,
        by rw [rp_fst]; exact hja, ?_⟩⟩
      rw [dd_rp_tr L a P _ hm]
      exact hc
    have hpos : dd L a P (x a) = 0 ∨ dd L a P (x a) = h := by
      by_contra hne
      rw [Nat.mod_eq_of_lt (by omega)] at c2
      omega
    have k1 := memR_ne L a P h hia x hpos
    have k4 := memR_ne L a P h hja x hpos
    have k2 := memR_ne L a P h hja (rshift L i x) (by rw [rshift_ne' L (Ne.symm hia)]; exact hpos)
    have k3 := memR_ne L a P h hia (rshift L j x) (by rw [rshift_ne' L (Ne.symm hja)]; exact hpos)
    simp only [rhol]
    rw [hUV _ k1, hUV _ k2, hUV _ k3, hUV _ k4]

/-! ## 4. The action split and reflection positivity -/

/-- The action of the left half. -/
def Aact (U : RLink L → SUN.SU 2) : ℝ := ∑ q, if plL L a P h q then wd (rhol L q U) else 0

/-- The action of the fixed planes. -/
def Cact (U : RLink L → SUN.SU 2) : ℝ :=
  ∑ q, if ¬ plL L a P h q ∧ ¬ plL L a P h (rp L a P q) then wd (rhol L q U) else 0

/-- **The action split**: `S = S_left + S_left ∘ Θ + S_planes`. -/
theorem action_split (hL : L a = 2 * h) (U : RLink L → SUN.SU 2) :
    ∑ q, wd (rhol L q U) = Aact L a P h U + Aact L a P h (Θ L a P U) + Cact L a P h U := by
  have hpt : ∀ q, wd (rhol L q U) = (if plL L a P h q then wd (rhol L q U) else 0)
      + (if plL L a P h (rp L a P q) then wd (rhol L q U) else 0)
      + (if ¬ plL L a P h q ∧ ¬ plL L a P h (rp L a P q) then wd (rhol L q U) else 0) := by
    intro q
    have := not_plL_both L a P h hL q
    by_cases h1 : plL L a P h q <;> by_cases h2 : plL L a P h (rp L a P q) <;> simp_all
  have hmid : ∑ q, (if plL L a P h (rp L a P q) then wd (rhol L q U) else 0)
      = Aact L a P h (Θ L a P U) := by
    unfold Aact
    have := Equiv.sum_comp (ρp L a P)
      (fun q => if plL L a P h q then wd (rhol L (rp L a P q) U) else 0)
    simp only [ρp, Function.Involutive.coe_toPerm, rp_invol L a P _] at this
    rw [this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [wd_refl_one]
  rw [Finset.sum_congr rfl fun q _ => hpt q, Finset.sum_add_distrib, Finset.sum_add_distrib, hmid]
  rfl

theorem Cact_reads (hL : L a = 2 * h) (U V : RLink L → SUN.SU 2)
    (hUV : ∀ l ∈ Rset L a P h, U l = V l) : Cact L a P h U = Cact L a P h V := by
  unfold Cact
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs with hc
  · by_cases hd : q.1.1 = q.1.2
    · obtain ⟨⟨i, j⟩, x⟩ := q
      simp only at hd
      subst hd
      rw [rhol_diag', rhol_diag']
    · rw [rest_reads L a P h hL q hd hc.1 hc.2 U V hUV]
  · rfl

theorem Aact_reads (hL : L a = 2 * h) (U V : RLink L → SUN.SU 2)
    (hUV : ∀ l ∈ Sset L a P h ∪ Rset L a P h, U l = V l) : Aact L a P h U = Aact L a P h V := by
  unfold Aact
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs with hc
  · rw [plL_reads L a P h hL q hc U V hUV]
  · rfl

omit [NeZero (L a)] in
theorem continuous_Aact : Continuous (Aact L a P h) :=
  continuous_finsetSum _ fun q _ => by
    split_ifs
    · exact WilsonAction.continuous_wilsonDensity.comp (continuous_rhol L q)
    · exact continuous_const

omit [NeZero (L a)] in
theorem continuous_Cact : Continuous (Cact L a P h) :=
  continuous_finsetSum _ fun q _ => by
    split_ifs
    · exact WilsonAction.continuous_wilsonDensity.comp (continuous_rhol L q)
    · exact continuous_const

theorem E_split (hL : L a = 2 * h) (β : ℝ) (U : RLink L → SUN.SU 2) :
    E L β U = Real.exp (-β * Cact L a P h U) * Real.exp (-β * Aact L a P h U)
      * Real.exp (-β * Aact L a P h (Θ L a P U)) := by
  unfold E
  rw [action_split L a P h hL U, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- **Reflection positivity of the Wilson measure on the rectangular torus**, at every real `β`, for
the site reflection in direction `a` about `x_a = P` (`L_a = 2h`): `∫ G · (G ∘ Θ) · e^{−βS} ≥ 0` for
every continuous `G` that reads the left half and the two fixed planes only. -/
theorem rp_nonneg (hL : L a = 2 * h) (β : ℝ) (G : (RLink L → SUN.SU 2) → ℝ) (hG : Continuous G)
    (hGl : ∀ U V, (∀ l ∈ Sset L a P h ∪ Rset L a P h, U l = V l) → G U = G V) :
    0 ≤ ∫ U, G U * G (Θ L a P U) * E L β U ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)) := by
  set Wt : (RLink L → SUN.SU 2) → ℝ := fun U => Real.exp (-β * Cact L a P h U) with hWt
  set O : (RLink L → SUN.SU 2) → ℝ := fun U => G U * Real.exp (-β * Aact L a P h U) with hO
  have hsplit : (fun U => G U * G (Θ L a P U) * E L β U)
      = fun U => Wt U * O U * O (twist (θp L a P) (σi L a) U) := by
    funext U
    rw [E_split L a P h hL β U]
    simp only [hWt, hO]
    unfold Θ
    ring
  rw [hsplit]
  have hOc : Continuous O := hG.mul (Real.continuous_exp.comp
    (continuous_const.mul (continuous_Aact L a P h)))
  have hWc : Continuous Wt := Real.continuous_exp.comp
    (continuous_const.mul (continuous_Cact L a P h))
  have hFc : Continuous fun U => Wt U * O U * O (twist (θp L a P) (σi L a) U) :=
    (hWc.mul hOc).mul (hOc.comp (continuous_Θ L a P))
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hFc.continuousOn
  refine pairing_nonneg_of_local (probHaar (SUN.SU 2)) (Sset L a P h) (Tset L a P h) (Rset L a P h)
    (disj_ST L a P h) (disj_SR L a P h) (disj_TR L a P h) (θp L a P) (σi L a) (σi_mp L a)
    (θ_fix_R L a P h hL) (σ_fix_R L a P h) (θ_S_T L a P h hL) (fun _ => 1) O hOc.measurable ?_
    Wt hWc.measurable (fun U => (Real.exp_pos _).le) ?_ C (fun U => ?_)
  · intro U V hS hR
    have hUV : ∀ l ∈ Sset L a P h ∪ Rset L a P h, U l = V l := by
      intro l hl
      rcases Finset.mem_union.1 hl with hl | hl
      · exact hS l hl
      · exact hR l hl
    simp only [hO]
    rw [hGl U V hUV, Aact_reads L a P h hL U V hUV]
  · intro U V hR
    simp only [hWt]
    rw [Cact_reads L a P h hL U V hR]
  · have := hC U (Set.mem_univ _)
    rwa [Real.norm_eq_abs] at this

/-- The reflection pairing `⟨G, H⟩_Θ = ∫ G · (H ∘ Θ) · e^{−βS}`. -/
def bil (β : ℝ) (G H : (RLink L → SUN.SU 2) → ℝ) : ℝ :=
  ∫ U, G U * H (Θ L a P U) * E L β U ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))

theorem integrable_bil (β : ℝ) {G H : (RLink L → SUN.SU 2) → ℝ} (hG : Continuous G)
    (hH : Continuous H) : Integrable (fun U => G U * H (Θ L a P U) * E L β U)
      (Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)) :=
  integrable_of_continuous ((hG.mul (hH.comp (continuous_Θ L a P))).mul (continuous_E L β))

theorem bil_symm (β : ℝ) {G H : (RLink L → SUN.SU 2) → ℝ} (hG : Continuous G)
    (hH : Continuous H) : bil L a P β G H = bil L a P β H G := by
  have hmp := Θ_mp L a P
  unfold bil
  conv_lhs => rw [← hmp.map_eq]
  rw [integral_map (f := fun U => G U * H (Θ L a P U) * E L β U) hmp.measurable.aemeasurable
    ((hG.mul (hH.comp (continuous_Θ L a P))).mul (continuous_E L β)).aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only [Θ_Θ, E_Θ]
  ring

/-- **The reflection Cauchy–Schwarz inequality** on the rectangular torus:
`⟨G, H⟩_Θ² ≤ ⟨G, G⟩_Θ ⟨H, H⟩_Θ` for continuous `G`, `H` reading the left half and the planes. -/
theorem bil_sq_le (hL : L a = 2 * h) (β : ℝ) {G H : (RLink L → SUN.SU 2) → ℝ} (hG : Continuous G)
    (hGl : ∀ U V, (∀ l ∈ Sset L a P h ∪ Rset L a P h, U l = V l) → G U = G V)
    (hH : Continuous H)
    (hHl : ∀ U V, (∀ l ∈ Sset L a P h ∪ Rset L a P h, U l = V l) → H U = H V) :
    bil L a P β G H ^ 2 ≤ bil L a P β G G * bil L a P β H H := by
  apply sq_le_of_quad
  intro t
  have hp := rp_nonneg L a P h hL β (fun U => G U + t * H U) (hG.add (continuous_const.mul hH))
    (fun U V hUV => by rw [hGl U V hUV, hHl U V hUV])
  have hsym := bil_symm L a P β hH hG
  have hexp : (fun U => (G U + t * H U) * (G (Θ L a P U) + t * H (Θ L a P U)) * E L β U)
      = fun U => G U * G (Θ L a P U) * E L β U + (t * (G U * H (Θ L a P U) * E L β U)
        + (t * (H U * G (Θ L a P U) * E L β U) + t ^ 2 * (H U * H (Θ L a P U) * E L β U))) := by
    funext U; ring
  rw [hexp, integral_add (integrable_bil L a P β hG hG), integral_add
    ((integrable_bil L a P β hG hH).const_mul t), integral_add
    ((integrable_bil L a P β hH hG).const_mul t) ((integrable_bil L a P β hH hH).const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul] at hp
  · change 0 ≤ bil L a P β G G + (t * bil L a P β G H + (t * bil L a P β H G
      + t ^ 2 * bil L a P β H H)) at hp
    rw [hsym] at hp
    linarith
  · exact ((integrable_bil L a P β hH hG).const_mul t).add
      ((integrable_bil L a P β hH hH).const_mul _)
  · exact ((integrable_bil L a P β hG hH).const_mul t).add
      (((integrable_bil L a P β hH hG).const_mul t).add ((integrable_bil L a P β hH hH).const_mul _))

theorem Θ_fix (hL : L a = 2 * h) (U : RLink L → SUN.SU 2) (l : RLink L) (hl : l ∈ Rset L a P h) :
    Θ L a P U l = U l := by
  show σi L a l (U (θp L a P l)) = U l
  rw [θ_fix_R L a P h hL l hl, σ_fix_R L a P h l hl]

end Refl

/-! ## 5. Real coordinates of an `SU(2)` matrix -/

/-- The eight real coordinates of an `SU(2)` element: real and imaginary parts of its entries. -/
def Xg (k : Fin 2 × Fin 2 × Bool) (g : SUN.SU 2) : ℝ :=
  if k.2.2 then ((g : Matrix (Fin 2) (Fin 2) ℂ) k.1 k.2.1).re
  else ((g : Matrix (Fin 2) (Fin 2) ℂ) k.1 k.2.1).im

theorem continuous_Xg (k : Fin 2 × Fin 2 × Bool) : Continuous (Xg k) := by
  unfold Xg
  split_ifs
  · exact Complex.continuous_re.comp (continuous_subtype_val.matrix_elem k.1 k.2.1)
  · exact Complex.continuous_im.comp (continuous_subtype_val.matrix_elem k.1 k.2.1)

/-- **The real form of `Re tr(A B⁻¹)`**: `Σ_k X_k(A) X_k(B) = 2 (1 − wd(A B⁻¹))`. -/
theorem sumX (A B : SUN.SU 2) :
    ∑ k : Fin 2 × Fin 2 × Bool, Xg k A * Xg k B = 2 * (1 - wd (A * B⁻¹)) := by
  have hB : ((A * B⁻¹ : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ)
      = (A : Matrix (Fin 2) (Fin 2) ℂ) * star (B : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  unfold WilsonAction.wilsonDensity
  rw [hB]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, Xg, if_true,
    Bool.false_eq_true, if_false, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.star_apply,
    Complex.add_re, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

theorem sumX_self (B : SUN.SU 2) : ∑ k : Fin 2 × Fin 2 × Bool, Xg k B * Xg k B = 2 := by
  rw [sumX, mul_inv_cancel, WilsonAction.wilsonDensity_one (N := 2) (by norm_num)]
  ring

/-! ## 6. Paths and the rectangle -/

section Paths

variable (L : Fin 4 → ℕ)

/-- The ordered product of the `k` links along `i` leaving `y`. -/
def path (i : Fin 4) (y : RSite L) (k : ℕ) (U : RLink L → SUN.SU 2) : SUN.SU 2 :=
  ((List.range k).map fun t => U (i, (rshift L i)^[t] y)).prod

theorem continuous_path (i : Fin 4) (y : RSite L) (k : ℕ) :
    Continuous (path L i y k) :=
  continuous_list_prod _ fun _ _ => continuous_apply _

theorem path_congr (i : Fin 4) (y : RSite L) (k : ℕ) (U V : RLink L → SUN.SU 2)
    (h : ∀ t < k, U (i, (rshift L i)^[t] y) = V (i, (rshift L i)^[t] y)) :
    path L i y k U = path L i y k V := by
  unfold path
  congr 1
  exact List.map_congr_left fun t ht => h t (List.mem_range.1 ht)

theorem path_add (i : Fin 4) (y : RSite L) (m k : ℕ) (U : RLink L → SUN.SU 2) :
    path L i y (m + k) U = path L i y m U * path L i ((rshift L i)^[m] y) k U := by
  unfold path
  rw [List.range_add, List.map_append, List.prod_append, List.map_map]
  congr 1
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply]
  rw [add_comm, Function.iterate_add_apply]

/-- **The rectangle holonomy** as bottom · right · top⁻¹ · left⁻¹. -/
theorem rectHol_eq (a b : Fin 4) (m n : ℕ) (o : RSite L) (U : RLink L → SUN.SU 2) :
    wHol L (VortexCondense.rectWord L a b m n o) U
      = path L a o m U * path L b ((rshift L a)^[m] o) n U * (path L a ((rshift L b)^[n] o) m U)⁻¹
        * (path L b o n U)⁻¹ := by
  simp only [wHol, VortexCondense.rectWord, path, List.map_append, List.prod_append,
    List.map_reverse, List.map_map, List.prod_inv_reverse, Function.comp_def, if_true,
    Bool.false_eq_true, if_false]

theorem prod_range_inv {G : Type*} [Group G] (g : ℕ → G) (m : ℕ) :
    ((List.range m).map g).prod⁻¹ = ((List.range m).map fun t => (g (m - 1 - t))⁻¹).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
      conv_lhs => rw [List.range_succ, List.map_append, List.prod_append, mul_inv_rev, ih]
      conv_rhs => rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        Function.comp_def, Nat.add_sub_cancel, Nat.sub_zero]
      congr 1
      congr 1
      refine List.map_congr_left fun t _ => ?_
      congr 2
      omega

end Paths

/-! ## 7. Reflecting the rectangle -/

section ReflRect

open Fin.NatCast Fin.CommRing

variable (L : Fin 4 → ℕ) (a : Fin 4) [NeZero (L a)] (P : Fin (L a))

theorem iter_a (x : RSite L) (k : ℕ) : ((rshift L a)^[k] x) a = x a + (k : Fin (L a)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', rshift_self, ih]
      push_cast
      ring

theorem site_ext (x y : RSite L) (ha : x a = y a) (hc : ∀ c, c ≠ a → x c = y c) : x = y := by
  funext c
  by_cases h : c = a
  · subst h; exact ha
  · exact hc c h

theorem rs_iter_b {b : Fin 4} (hb : b ≠ a) (t : ℕ) (y : RSite L) :
    rs L a P ((rshift L b)^[t] y) = (rshift L b)^[t] (rs L a P y) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', rs_rshift L a P hb, ih]

theorem rs_iter_a {m : ℕ} (y : RSite L) (hy : y a + (m : Fin (L a)) = P) (t k : ℕ)
    (htk : t + 1 + k = 2 * m) : rs L a P ((rshift L a)^[t + 1] y) = (rshift L a)^[k] y := by
  apply site_ext L a
  · rw [rs_self, iter_a, iter_a]
    have hk : ((t + 1 + k : ℕ) : Fin (L a)) = ((2 * m : ℕ) : Fin (L a)) := by rw [htk]
    push_cast at hk ⊢
    linear_combination (-2 : Fin (L a)) * hy - hk
  · intro c hc
    rw [rs_ne L a P hc, iter_ne L hc, iter_ne L hc]

theorem rs_corner {m : ℕ} (y : RSite L) (hy : y a + (m : Fin (L a)) = P) :
    rs L a P y = (rshift L a)^[2 * m] y := by
  apply site_ext L a
  · rw [rs_self, iter_a]
    push_cast
    linear_combination (-2 : Fin (L a)) * hy
  · intro c hc
    rw [rs_ne L a P hc, iter_ne L hc]

/-- **The bottom of the rectangle reflects to the inverse of the bottom of its mirror image.** -/
theorem pathA_Θ {m : ℕ} (y : RSite L) (hy : y a + (m : Fin (L a)) = P) (U : RLink L → SUN.SU 2) :
    path L a y m (Θ L a P U) = (path L a ((rshift L a)^[m] y) m U)⁻¹ := by
  unfold path
  rw [prod_range_inv]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  have ht' := List.mem_range.1 ht
  rw [Θ_a, ← Function.iterate_succ_apply' (rshift L a), Nat.succ_eq_add_one,
    rs_iter_a L a P y hy t (2 * m - 1 - t) (by omega), ← Function.iterate_add_apply,
    show m - 1 - t + m = 2 * m - 1 - t by omega]

theorem pathB_Θ {b : Fin 4} (hb : b ≠ a) (y : RSite L) (n : ℕ) (U : RLink L → SUN.SU 2) :
    path L b y n (Θ L a P U) = path L b (rs L a P y) n U := by
  unfold path
  congr 1
  refine List.map_congr_left fun t _ => ?_
  rw [Θ_ne L a P hb, rs_iter_b L a P hb]

end ReflRect

/-! ## 8. Flux operators: reflection, readings, and the projection identity -/

section Flux

open Fin.NatCast Fin.CommRing
open MassGap.TwistedTraceBound (negOne negOne_mul_self)

variable (L : Fin 4 → ℕ)

theorem sheetAt_central (a b : Fin 4) (pa : Fin (L a)) (pb : Fin (L b)) (q : RPlaq L) :
    (∀ k, sheetAt L a b pa pb q * k = k * sheetAt L a b pa pb q)
      ∧ (sheetAt L a b pa pb q)⁻¹ = sheetAt L a b pa pb q := by
  unfold sheetAt
  split_ifs
  · exact ⟨negOne_comm, negOne_inv'⟩
  · exact ⟨fun k => by rw [one_mul, mul_one], inv_one⟩

theorem vortexOp_prod (β : ℝ) (ζ₁ ζ₂ : RPlaq L → SUN.SU 2) (hd : ∀ q, ζ₁ q = 1 ∨ ζ₂ q = 1)
    (U : RLink L → SUN.SU 2) :
    vortexOp L β ζ₁ U * vortexOp L β ζ₂ U = vortexOp L β (fun q => ζ₁ q * ζ₂ q) U := by
  have hs : (∑ q, (wd (ζ₁ q * rhol L q U) - wd (rhol L q U)))
      + ∑ q, (wd (ζ₂ q * rhol L q U) - wd (rhol L q U))
      = ∑ q, (wd (ζ₁ q * ζ₂ q * rhol L q U) - wd (rhol L q U)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rcases hd q with h | h <;> simp [h]
  unfold vortexOp
  rw [← Real.exp_add, ← mul_add, hs]

theorem continuous_vortexOp (β : ℝ) (ζ : RPlaq L → SUN.SU 2) : Continuous (vortexOp L β ζ) :=
  Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun q _ =>
    (WilsonAction.continuous_wilsonDensity.comp (continuous_const.mul (continuous_rhol L q))).sub
      (WilsonAction.continuous_wilsonDensity.comp (continuous_rhol L q))))

theorem continuous_fluxOp (β : ℝ) (ζ : RPlaq L → SUN.SU 2) : Continuous (fluxOp L β ζ) :=
  (continuous_const.sub (continuous_vortexOp L β ζ)).div_const _

theorem continuous_wObs (w : List (RLink L × Bool)) : Continuous (wObs L w) :=
  continuous_const.sub (WilsonAction.continuous_wilsonDensity.comp (continuous_wHol L w))

theorem int_E (β : ℝ) :
    ∫ U, E L β U ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)) = ZRp L β (fun _ => 1) := by
  unfold ZRp E
  simp only [one_mul]

theorem int_eq_ev (β : ℝ) (X : (RLink L → SUN.SU 2) → ℝ) :
    ∫ U, X U * E L β U ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))
      = ev L β X * ZRp L β (fun _ => 1) := by
  unfold ev
  rw [div_mul_cancel₀ _ (ZRp_pos L β _).ne']
  rfl

/-- `∫ F[ζ] W_w e^{−βS} = (WN(1) − WN(ζ))/2`. -/
theorem int_flux_wObs (w : List (RLink L × Bool)) (β : ℝ) (ζ : RPlaq L → SUN.SU 2) :
    ∫ U, fluxOp L β ζ U * wObs L w U * E L β U ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))
      = (WN L w β (fun _ => 1) - WN L w β ζ) / 2 := by
  rw [int_eq_ev L β (fun U => fluxOp L β ζ U * wObs L w U), ev_fluxOp_wObs]
  field_simp [(ZRp_pos L β (fun _ => 1)).ne']

/-- **Two flux operators with disjoint sheets**:
`∫ F[ζ₁] F[ζ₂] W_w e^{−βS} = (WN(1) − WN(ζ₁) − WN(ζ₂) + WN(ζ₁ζ₂))/4`. -/
theorem int_flux2_wObs (w : List (RLink L × Bool)) (β : ℝ) (ζ₁ ζ₂ : RPlaq L → SUN.SU 2)
    (hd : ∀ q, ζ₁ q = 1 ∨ ζ₂ q = 1) :
    ∫ U, fluxOp L β ζ₁ U * fluxOp L β ζ₂ U * wObs L w U * E L β U
        ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))
      = (WN L w β (fun _ => 1) - WN L w β ζ₁ - WN L w β ζ₂ + WN L w β (fun q => ζ₁ q * ζ₂ q)) / 4 := by
  set B : (RPlaq L → SUN.SU 2) → (RLink L → SUN.SU 2) → ℝ := fun ζ U =>
    (1 - wd (wHol L w U)) * Real.exp (-β * ∑ q, wd (ζ q * rhol L q U)) with hB
  have hpt : ∀ U, fluxOp L β ζ₁ U * fluxOp L β ζ₂ U * wObs L w U * E L β U
      = (B (fun _ => 1) U - B ζ₁ U - B ζ₂ U + B (fun q => ζ₁ q * ζ₂ q) U) / 4 := by
    intro U
    have e0 : Real.exp (-β * ∑ q, wd (1 * rhol L q U)) = E L β U := by
      simp only [one_mul]; rfl
    have e1 := (vortexOp_mul L β ζ₁ U).symm
    have e2 := (vortexOp_mul L β ζ₂ U).symm
    have e12 : Real.exp (-β * ∑ q, wd (ζ₁ q * ζ₂ q * rhol L q U))
        = vortexOp L β ζ₁ U * vortexOp L β ζ₂ U * E L β U := by
      rw [vortexOp_prod L β ζ₁ ζ₂ hd U]
      exact (vortexOp_mul L β (fun q => ζ₁ q * ζ₂ q) U).symm
    simp only [hB]
    rw [e0, e1, e2, e12]
    unfold fluxOp wObs E
    ring
  have hi : ∀ ζ, Integrable (B ζ) (Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)) :=
    fun ζ => integrable_of_continuous (continuous_WN_integrand L w β ζ)
  have h2 : Integrable (fun U => B (fun _ => 1) U - B ζ₁ U)
      (Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)) := (hi _).sub (hi _)
  have h3 : Integrable (fun U => B (fun _ => 1) U - B ζ₁ U - B ζ₂ U)
      (Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)) := h2.sub (hi _)
  simp_rw [hpt]
  rw [integral_div, integral_add h3 (hi _), integral_sub h2 (hi _), integral_sub (hi _) (hi _)]
  rfl

/-- **One step of a sheet times any pattern**, across a step set the word does not meet. -/
theorem WN_step_mul {a b : Fin 4} (hab : a ≠ b) (s : Fin (L a)) (pb : Fin (L b))
    (w : List (RLink L × Bool)) (β : ℝ) (Y : RPlaq L → SUN.SU 2)
    (hc : wCount L (stepSet L a b s pb) w = 0) :
    WN L w β (fun q => sheetAt L a b ((finRotate (L a)).symm s) pb q * Y q)
      = WN L w β (fun q => sheetAt L a b s pb q * Y q) := by
  have := WN_flip L (stepSet L a b s pb) w β (fun q => sheetAt L a b s pb q * Y q)
    (fun q => sheetAt L a b ((finRotate (L a)).symm s) pb q * Y q)
    (fun q => by rw [sheet_step L hab s pb q, mul_assoc])
  rw [hc, pow_zero, one_mul] at this
  exact this.symm

theorem WN_step {a b : Fin 4} (hab : a ≠ b) (s : Fin (L a)) (pb : Fin (L b))
    (w : List (RLink L × Bool)) (β : ℝ) (hc : wCount L (stepSet L a b s pb) w = 0) :
    WN L w β (sheetAt L a b ((finRotate (L a)).symm s) pb) = WN L w β (sheetAt L a b s pb) := by
  have := WN_step_mul L hab s pb w β (fun _ => 1) hc
  simpa only [mul_one] using this

theorem sheetAt_sq (a b : Fin 4) (pa : Fin (L a)) (pb : Fin (L b)) :
    (fun q => sheetAt L a b pa pb q * sheetAt L a b pa pb q) = fun _ => 1 := by
  funext q
  unfold sheetAt
  split_ifs
  · exact negOne_mul_self
  · exact mul_one 1

/-- **The step set meets a rectangle only on its two `b`-sides.** -/
theorem count_zero {a b : Fin 4} (hab : a ≠ b) (s : Fin (L a)) (pb : Fin (L b)) (M n : ℕ)
    (o : RSite L) (h1 : s ≠ o a) (h2 : s ≠ ((rshift L a)^[M] o) a) :
    wCount L (stepSet L a b s pb) (VortexCondense.rectWord L a b M n o) = 0 := by
  unfold wCount VortexCondense.rectWord
  simp only [List.countP_append, List.countP_reverse, List.countP_map]
  have hA : ∀ (y : ℕ → RSite L) (k : ℕ) (sg : Bool),
      List.countP ((fun lo : RLink L × Bool => stepSet L a b s pb lo.1) ∘
        (fun t => ((a, y t), sg))) (List.range k) = 0 := by
    intro y k sg
    refine List.countP_eq_zero.2 fun t _ => ?_
    simp [stepSet, hab]
  have hB : ∀ (y : RSite L) (sg : Bool), y a ≠ s →
      List.countP ((fun lo : RLink L × Bool => stepSet L a b s pb lo.1) ∘
        (fun t => ((b, (rshift L b)^[t] y), sg))) (List.range n) = 0 := by
    intro y sg hy
    refine List.countP_eq_zero.2 fun t _ => ?_
    simp [stepSet, iter_ne L hab, hy]
  rw [hA, hA, hB _ _ (Ne.symm h2), hB _ _ (Ne.symm h1)]

end Flux

section FluxRefl

open Fin.NatCast Fin.CommRing

variable (L : Fin 4 → ℕ) (a : Fin 4) [NeZero (L a)] (P : Fin (L a))

/-- **The vortex operator under the reflection** reads the mirrored pattern. -/
theorem vortexOp_Θ (β : ℝ) (ζ : RPlaq L → SUN.SU 2)
    (hζ : ∀ q, (∀ k, ζ q * k = k * ζ q) ∧ (ζ q)⁻¹ = ζ q) (U : RLink L → SUN.SU 2) :
    vortexOp L β ζ (Θ L a P U) = vortexOp L β (fun q => ζ (rp L a P q)) U := by
  have hs : ∑ q, (wd (ζ q * rhol L q (Θ L a P U)) - wd (rhol L q (Θ L a P U)))
      = ∑ q, (wd (ζ (rp L a P q) * rhol L q U) - wd (rhol L q U)) := by
    rw [Finset.sum_congr rfl fun q _ => by
      rw [wd_refl L a P (ζ q) (hζ q).1 (hζ q).2 q U, wd_refl_one L a P q U]]
    have := Equiv.sum_comp (ρp L a P)
      (fun q => wd (ζ (rp L a P q) * rhol L q U) - wd (rhol L q U))
    simp only [ρp, Function.Involutive.coe_toPerm, rp_invol L a P _] at this
    exact this
  unfold vortexOp
  rw [hs]

theorem fluxOp_Θ (β : ℝ) (ζ : RPlaq L → SUN.SU 2)
    (hζ : ∀ q, (∀ k, ζ q * k = k * ζ q) ∧ (ζ q)⁻¹ = ζ q) (U : RLink L → SUN.SU 2) :
    fluxOp L β ζ (Θ L a P U) = fluxOp L β (fun q => ζ (rp L a P q)) U := by
  unfold fluxOp
  rw [vortexOp_Θ L a P β ζ hζ U]

/-- **The mirror image of a sheet** at `x_a = p_a` is the sheet at `x_a = 2P − 1 − p_a`. -/
theorem sheet_rp {b : Fin 4} (hab : a ≠ b) (pa : Fin (L a)) (pb : Fin (L b)) :
    (fun q => sheetAt L a b pa pb (rp L a P q)) = sheetAt L a b (P + P - (pa + 1)) pb := by
  funext q
  obtain ⟨⟨i, j⟩, x⟩ := q
  unfold sheetAt
  by_cases hq : (i, j) = (a, b) ∨ (i, j) = (b, a)
  · have hm : i = a ∨ j = a := by
      rcases hq with h | h <;> simp only [Prod.mk.injEq] at h <;> tauto
    have hr : rp L a P ((i, j), x) = ((i, j), rs L a P (rshift L a x)) := by simp [rp, hm]
    rw [hr]
    simp only [hq, true_and]
    rw [rs_self, rshift_self, rs_ne L a P (Ne.symm hab), rshift_ne' L (Ne.symm hab)]
    refine if_congr ⟨fun ⟨h1, h2⟩ => ⟨?_, h2⟩, fun ⟨h1, h2⟩ => ⟨?_, h2⟩⟩ rfl rfl
    · rw [← h1]; ring
    · rw [h1]; ring
  · have : (rp L a P ((i, j), x)).1 = (i, j) := rp_fst L a P _
    simp only [this, hq, false_and, if_false]

variable (h : ℕ)

/-- **A vortex operator reads the plaquettes of its pattern**: if every plaquette where the pattern is
not `1` lies in the left half, the operator reads the left half and the planes only. -/
theorem vortexOp_reads (hL : L a = 2 * h) (β : ℝ) (ζ : RPlaq L → SUN.SU 2)
    (hζ : ∀ q, ζ q ≠ 1 → plL L a P h q) (U V : RLink L → SUN.SU 2)
    (hUV : ∀ l ∈ Sset L a P h ∪ Rset L a P h, U l = V l) : vortexOp L β ζ U = vortexOp L β ζ V := by
  have hs : ∑ q, (wd (ζ q * rhol L q U) - wd (rhol L q U))
      = ∑ q, (wd (ζ q * rhol L q V) - wd (rhol L q V)) := by
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : ζ q = 1
    · rw [hq, one_mul, one_mul, sub_self, sub_self]
    · rw [plL_reads L a P h hL q (hζ q hq) U V hUV]
  unfold vortexOp
  rw [hs]

theorem dd_before (v : Fin (L a)) (k : ℕ) (hv : v + (k : Fin (L a)) = P) (hk0 : 0 < k)
    (hkL : k < L a) : dd L a P v = L a - k := by
  unfold dd
  have : v - P = -(k : Fin (L a)) := by rw [← hv]; ring
  rw [this, Fin.val_neg', Fin.val_natCast, Nat.mod_eq_of_lt hkL, Nat.mod_eq_of_lt (by omega)]

theorem dd_self : dd L a P P = 0 := by
  unfold dd; rw [sub_self, Fin.val_zero]

end FluxRefl

/-! ## 9. One Schwarz doubling of the rectangle -/

section Doubling

open Fin.NatCast Fin.CommRing

variable (L : Fin 4 → ℕ)

/-- **One Schwarz doubling** (Kanazawa eqs. (34)–(39) at `N = 2`). For `a ≠ b`, `L_a = 2h` and
`0 < m ≤ h`, with the flux operator of the sheet inside the far side of the `m × n` rectangle:
`⟨F[sIn] W(m × n)⟩² ≤ ⟨F[sIn] W(2m × n)⟩`, and the right side is `≥ 0`. The reflection is the site
reflection about the far side `x_a = x_a(o) + m`. -/
theorem doubling {a b : Fin 4} (hab : a ≠ b) (h : ℕ) (hL : L a = 2 * h) (o : RSite L) {m : ℕ}
    (hm : 0 < m) (hmh : m ≤ h) (n : ℕ) (β : ℝ) :
    ev L β (fun U => fluxOp L β (sIn L a b m o) U
        * wObs L (VortexCondense.rectWord L a b m n o) U) ^ 2
      ≤ ev L β (fun U => fluxOp L β (sIn L a b m o) U
          * wObs L (VortexCondense.rectWord L a b (2 * m) n o) U)
    ∧ 0 ≤ ev L β (fun U => fluxOp L β (sIn L a b m o) U
          * wObs L (VortexCondense.rectWord L a b (2 * m) n o) U) := by
  haveI : NeZero (L a) := ⟨by omega⟩
  have hba : b ≠ a := Ne.symm hab
  set P : Fin (L a) := farA L a m o with hPdef
  have hP : o a + (m : Fin (L a)) = P := by rw [hPdef, farA, iter_a]
  have hsym : (finRotate (L a)).symm P + 1 = P := by
    rw [← finRotate_eq_add_one, Equiv.apply_symm_apply]
  have hζ₁ : sIn L a b m o = sheetAt L a b ((finRotate (L a)).symm P) (o b) := by rw [hPdef]; rfl
  rw [hζ₁]
  set ζ₁ := sheetAt L a b ((finRotate (L a)).symm P) (o b) with hz1
  set ζ₂ := sheetAt L a b P (o b) with hz2
  set μ := Measure.pi fun _ : RLink L => probHaar (SUN.SU 2) with hμ
  -- the four sides
  set Bot : (RLink L → SUN.SU 2) → SUN.SU 2 := path L a o m with hBot
  set Top : (RLink L → SUN.SU 2) → SUN.SU 2 := path L a ((rshift L b)^[n] o) m with hTop
  set Lf : (RLink L → SUN.SU 2) → SUN.SU 2 := path L b o n with hLf
  set Rt : (RLink L → SUN.SU 2) → SUN.SU 2 := path L b ((rshift L a)^[m] o) n with hRt
  set Mh : (RLink L → SUN.SU 2) → SUN.SU 2 := fun U => (Top U)⁻¹ * (Lf U)⁻¹ * Bot U with hMh
  -- positions
  have hddA : ∀ t < m, h ≤ dd L a P (o a + (t : Fin (L a))) := by
    intro t ht
    rw [dd_before L a P _ (m - t) (by rw [← hP]; push_cast [Nat.cast_sub ht.le]; ring)
      (by omega) (by omega)]
    omega
  have hddLf : h ≤ dd L a P (o a) := by
    rw [dd_before L a P _ m hP hm (by omega)]; omega
  have hRtR : ∀ t < n, (b, (rshift L b)^[t] ((rshift L a)^[m] o)) ∈ Rset L a P h := fun t _ =>
    memR_ne L a P h hba _ (Or.inl (by rw [iter_ne L hab, ← farA, ← hPdef, dd_self]))
  have hRtΘ : ∀ U, Rt (Θ L a P U) = Rt U := fun U =>
    path_congr L b _ n _ _ fun t ht => Θ_fix L a P h hL U _ (hRtR t ht)
  have hRt_r : ∀ U V : RLink L → SUN.SU 2, (∀ l ∈ Sset L a P h ∪ Rset L a P h, U l = V l) →
      Rt U = Rt V := fun U V hUV =>
    path_congr L b _ n _ _ fun t ht => hUV _ (Finset.mem_union_right _ (hRtR t ht))
  have hMh_r : ∀ U V : RLink L → SUN.SU 2, (∀ l ∈ Sset L a P h ∪ Rset L a P h, U l = V l) →
      Mh U = Mh V := by
    intro U V hUV
    have e1 : Top U = Top V := path_congr L a _ m _ _ fun t ht => hUV _ (memSR_a L a P h _
      (by rw [iter_a, iter_ne L hab]; exact hddA t ht))
    have e2 : Lf U = Lf V := path_congr L b _ n _ _ fun t _ => hUV _ (memSR_ne L a P h hba _
      (Or.inl (by rw [iter_ne L hab]; exact hddLf)))
    have e3 : Bot U = Bot V := path_congr L a _ m _ _ fun t ht => hUV _ (memSR_a L a P h _
      (by rw [iter_a]; exact hddA t ht))
    simp only [hMh, e1, e2, e3]
  have hζpl : ∀ q, ζ₁ q ≠ 1 → plL L a P h q := by
    intro q hq
    simp only [hz1, sheetAt] at hq
    split_ifs at hq with hc
    · obtain ⟨hq1, hqa, -⟩ := hc
      refine ⟨?_, Or.inl ⟨?_, ?_⟩⟩
      · rcases hq1 with e | e <;> rw [e] <;> simp [hab, hba]
      · rcases hq1 with e | e <;> rw [e] <;> simp
      · rw [hqa, dd_before L a P _ 1 (by rw [Nat.cast_one]; exact hsym) one_pos (by omega)]
        omega
    · exact absurd rfl hq
  have hF_r : ∀ U V : RLink L → SUN.SU 2, (∀ l ∈ Sset L a P h ∪ Rset L a P h, U l = V l) →
      fluxOp L β ζ₁ U = fluxOp L β ζ₁ V := by
    intro U V hUV
    unfold fluxOp
    rw [vortexOp_reads L a P h hL β ζ₁ hζpl U V hUV]
  have hFΘ : ∀ U, fluxOp L β ζ₁ (Θ L a P U) = fluxOp L β ζ₂ U := by
    intro U
    rw [fluxOp_Θ L a P β ζ₁ (sheetAt_central L a b _ _) U, hz1, sheet_rp L a P hab, hsym,
      show P + P - P = P by ring]
  -- continuity
  have hBc : Continuous Bot := continuous_path L a o m
  have hTc : Continuous Top := continuous_path L a _ m
  have hLc : Continuous Lf := continuous_path L b o n
  have hRc : Continuous Rt := continuous_path L b _ n
  have hMc : Continuous Mh := (hTc.inv.mul hLc.inv).mul hBc
  have hFc : Continuous (fluxOp L β ζ₁) := continuous_fluxOp L β ζ₁
  -- the two families
  set G : Fin 2 × Fin 2 × Bool → (RLink L → SUN.SU 2) → ℝ :=
    fun k U => fluxOp L β ζ₁ U * Xg k (Mh U) with hG
  set H : Fin 2 × Fin 2 × Bool → (RLink L → SUN.SU 2) → ℝ :=
    fun k U => Xg k (Rt U)⁻¹ with hH
  have hGc : ∀ k, Continuous (G k) := fun k => hFc.mul ((continuous_Xg k).comp hMc)
  have hHc : ∀ k, Continuous (H k) := fun k => (continuous_Xg k).comp hRc.inv
  have hG_r : ∀ k U V, (∀ l ∈ Sset L a P h ∪ Rset L a P h, U l = V l) → G k U = G k V :=
    fun k U V hUV => by simp only [hG]; rw [hF_r U V hUV, hMh_r U V hUV]
  have hH_r : ∀ k U V, (∀ l ∈ Sset L a P h ∪ Rset L a P h, U l = V l) → H k U = H k V :=
    fun k U V hUV => by simp only [hH]; rw [hRt_r U V hUV]
  -- the rectangle as a reflection pairing
  have f1 : ∀ U, fluxOp L β ζ₁ U * wObs L (VortexCondense.rectWord L a b m n o) U * E L β U
      = 1 / 2 * ∑ k, G k U * H k (Θ L a P U) * E L β U := by
    intro U
    have hW : wObs L (VortexCondense.rectWord L a b m n o) U = 1 - wd (Mh U * Rt U) := by
      unfold wObs
      rw [rectHol_eq]
      have e : Bot U * Rt U * (Top U)⁻¹ * (Lf U)⁻¹
          = (Lf U * Top U) * (Mh U * Rt U) * (Lf U * Top U)⁻¹ := by simp only [hMh]; group
      rw [e, WilsonAction.wilsonDensity_conj]
    have hs : ∑ k, G k U * H k (Θ L a P U) = fluxOp L β ζ₁ U * (2 * (1 - wd (Mh U * Rt U))) := by
      simp only [hG, hH, hRtΘ, mul_assoc, ← Finset.mul_sum]
      rw [sumX, inv_inv]
    rw [← Finset.sum_mul, hs, hW]
    ring
  have hI1 : ∫ U, fluxOp L β ζ₁ U * wObs L (VortexCondense.rectWord L a b m n o) U * E L β U ∂μ
      = 1 / 2 * ∑ k, bil L a P β (G k) (H k) := by
    simp_rw [f1]
    rw [integral_const_mul, integral_finsetSum _ fun k _ => integrable_bil L a P β (hGc k) (hHc k)]
    rfl
  -- the doubled rectangle
  have hMΘ : ∀ U, Mh U * (Mh (Θ L a P U))⁻¹
      = ((Top U)⁻¹ * (Lf U)⁻¹) * wHol L (VortexCondense.rectWord L a b (2 * m) n o) U
        * ((Top U)⁻¹ * (Lf U)⁻¹)⁻¹ := by
    intro U
    have hy : ((rshift L b)^[n] o) a + (m : Fin (L a)) = P := by rw [iter_ne L hab]; exact hP
    simp only [hMh, hTop, hLf, hBot]
    rw [rectHol_eq, pathA_Θ L a P _ hy, pathB_Θ L a P hba, rs_corner L a P o hP, pathA_Θ L a P o hP,
      two_mul, path_add, path_add]
    group
  have f3 : ∀ U, ∑ k, G k U * G k (Θ L a P U) * E L β U
      = 2 * (fluxOp L β ζ₁ U * fluxOp L β ζ₂ U
        * wObs L (VortexCondense.rectWord L a b (2 * m) n o) U * E L β U) := by
    intro U
    have hs : ∑ k, G k U * G k (Θ L a P U)
        = fluxOp L β ζ₁ U * fluxOp L β ζ₂ U * (2 * (1 - wd (Mh U * (Mh (Θ L a P U))⁻¹))) := by
      simp only [hG, hFΘ]
      rw [← sumX, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [← Finset.sum_mul, hs, hMΘ, WilsonAction.wilsonDensity_conj]
    unfold wObs
    ring
  have f4 : ∀ U, ∑ k, H k U * H k (Θ L a P U) * E L β U = 2 * E L β U := by
    intro U
    simp only [hH, hRtΘ]
    rw [← Finset.sum_mul, sumX_self]
  have hsG : ∑ k, bil L a P β (G k) (G k) = 2 * ∫ U, fluxOp L β ζ₁ U * fluxOp L β ζ₂ U
      * wObs L (VortexCondense.rectWord L a b (2 * m) n o) U * E L β U ∂μ := by
    unfold bil
    rw [← integral_finsetSum _ fun k _ => integrable_bil L a P β (hGc k) (hGc k)]
    simp_rw [f3]
    rw [integral_const_mul]
  have hsH : ∑ k, bil L a P β (H k) (H k) = 2 * ZRp L β (fun _ => 1) := by
    unfold bil
    rw [← integral_finsetSum _ fun k _ => integrable_bil L a P β (hHc k) (hHc k)]
    simp_rw [f4]
    rw [integral_const_mul, int_E]
  -- the projection identity
  have hne : (finRotate (L a)).symm P ≠ P := by
    intro e
    rw [e] at hsym
    have h10 : (1 : Fin (L a)) = 0 := by linear_combination hsym
    have := congrArg Fin.val h10
    rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hdisj : ∀ q, ζ₁ q = 1 ∨ ζ₂ q = 1 := by
    intro q
    by_cases c2 : (q.1 = (a, b) ∨ q.1 = (b, a)) ∧ q.2 a = P ∧ q.2 b = o b
    · left
      simp only [hz1, sheetAt]
      rw [if_neg]
      intro c1
      exact hne (c1.2.1.symm.trans c2.2.1)
    · right
      simp only [hz2, sheetAt]
      rw [if_neg c2]
  have hmL : m < L a := by omega
  have hc : wCount L (stepSet L a b P (o b)) (VortexCondense.rectWord L a b (2 * m) n o) = 0 := by
    refine count_zero L hab P (o b) (2 * m) n o ?_ ?_
    · intro e
      have h0 : (m : Fin (L a)) = 0 := by linear_combination hP + e
      have := congrArg Fin.val h0
      rw [Fin.val_natCast, Fin.val_zero, Nat.mod_eq_of_lt hmL] at this
      omega
    · intro e
      rw [iter_a] at e
      push_cast at e
      have h0 : (m : Fin (L a)) = 0 := by linear_combination (-1 : Fin (L a)) * hP - e
      have := congrArg Fin.val h0
      rw [Fin.val_natCast, Fin.val_zero, Nat.mod_eq_of_lt hmL] at this
      omega
  have hWN1 : WN L (VortexCondense.rectWord L a b (2 * m) n o) β ζ₁
      = WN L (VortexCondense.rectWord L a b (2 * m) n o) β ζ₂ :=
    WN_step L hab P (o b) _ β hc
  have hWN12 : WN L (VortexCondense.rectWord L a b (2 * m) n o) β (fun q => ζ₁ q * ζ₂ q)
      = WN L (VortexCondense.rectWord L a b (2 * m) n o) β (fun _ => 1) := by
    rw [WN_step_mul L hab P (o b) _ β ζ₂ hc, hz2, sheetAt_sq]
  have hproj : ∫ U, fluxOp L β ζ₁ U * fluxOp L β ζ₂ U
      * wObs L (VortexCondense.rectWord L a b (2 * m) n o) U * E L β U ∂μ
      = ∫ U, fluxOp L β ζ₁ U * wObs L (VortexCondense.rectWord L a b (2 * m) n o) U * E L β U ∂μ := by
    rw [int_flux2_wObs L _ β ζ₁ ζ₂ hdisj, int_flux_wObs, hWN12, ← hWN1]
    ring
  -- Cauchy–Schwarz over the eight coordinates
  have hGnn : ∀ k ∈ (Finset.univ : Finset (Fin 2 × Fin 2 × Bool)), 0 ≤ bil L a P β (G k) (G k) :=
    fun k _ => rp_nonneg L a P h hL β (G k) (hGc k) (hG_r k)
  have hHnn : ∀ k ∈ (Finset.univ : Finset (Fin 2 × Fin 2 × Bool)), 0 ≤ bil L a P β (H k) (H k) :=
    fun k _ => rp_nonneg L a P h hL β (H k) (hHc k) (hH_r k)
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ hGnn hHnn
    (fun k _ => bil_sq_le L a P h hL β (hGc k) (hG_r k) (hHc k) (hH_r k))
  rw [hsG, hsH, hproj] at hCS
  have hX0 : 0 ≤ ∫ U, fluxOp L β ζ₁ U * wObs L (VortexCondense.rectWord L a b (2 * m) n o) U
      * E L β U ∂μ := by
    have := Finset.sum_nonneg hGnn
    rw [hsG, hproj] at this
    linarith
  have e1 := int_eq_ev L β (fun U => fluxOp L β ζ₁ U * wObs L (VortexCondense.rectWord L a b m n o) U)
  have e2 := int_eq_ev L β
    (fun U => fluxOp L β ζ₁ U * wObs L (VortexCondense.rectWord L a b (2 * m) n o) U)
  rw [hI1] at e1
  rw [e2] at hCS hX0
  set v1 := ev L β (fun U => fluxOp L β ζ₁ U * wObs L (VortexCondense.rectWord L a b m n o) U)
  set v2 := ev L β
    (fun U => fluxOp L β ζ₁ U * wObs L (VortexCondense.rectWord L a b (2 * m) n o) U)
  set Z := ZRp L β (fun _ => 1)
  have hZ : 0 < Z := ZRp_pos L β (fun _ => 1)
  have hsum : ∑ k, bil L a P β (G k) (H k) = 2 * (v1 * Z) := by linarith [e1]
  rw [hsum] at hCS
  constructor
  · have h4 : v1 ^ 2 * (4 * Z ^ 2) ≤ v2 * (4 * Z ^ 2) := by nlinarith [hCS]
    exact le_of_mul_le_mul_right h4 (by positivity)
  · exact (mul_nonneg_iff_of_pos_right hZ).1 hX0

end Doubling

/-! ## 10. Iterating the doubling, and the reduction of the inside half -/

section Chain

open Fin.NatCast Fin.CommRing

variable (L : Fin 4 → ℕ)

theorem pow_chain (x : ℕ → ℝ) :
    ∀ p : ℕ, (∀ j < p, x j ^ 2 ≤ x (j + 1) ∧ 0 ≤ x (j + 1)) → |x 0| ^ (2 ^ p) ≤ |x p|
  | 0, _ => by simp
  | p + 1, h => by
      have ih := pow_chain x p (fun j hj => h j (by omega))
      obtain ⟨h1, h2⟩ := h p (by omega)
      calc |x 0| ^ (2 ^ (p + 1)) = (|x 0| ^ (2 ^ p)) ^ 2 := by rw [pow_succ, pow_mul]
        _ ≤ |x p| ^ 2 := pow_le_pow_left₀ (by positivity) ih 2
        _ = x p ^ 2 := sq_abs _
        _ ≤ x (p + 1) := h1
        _ = |x (p + 1)| := (abs_of_nonneg h2).symm

theorem symm_finRotate_add_one {k : ℕ} [NeZero k] (v : Fin k) : (finRotate k).symm (v + 1) = v := by
  rw [Equiv.symm_apply_eq, finRotate_eq_add_one]

theorem sIn_eq (a b : Fin 4) [NeZero (L a)] (m : ℕ) (o : RSite L) :
    sIn L a b m o = sheetAt L a b ((finRotate (L a)).symm (o a + (m : Fin (L a)))) (o b) := by
  rw [sIn, farA, iter_a]

/-- **Moving the sheet inside the rectangle**: from `x_a = x_a(o) + m − 1` to `x_a(o) + m + k − 1`,
for `0 < m`, `m + k ≤ M ≤ L_a`, does not change the Wilson numerator of the `M × n` rectangle. -/
theorem WN_move {a b : Fin 4} (hab : a ≠ b) [NeZero (L a)] (o : RSite L) (pb : Fin (L b))
    {m M : ℕ} (n : ℕ) (hm : 0 < m) (hML : M ≤ L a) (β : ℝ) :
    ∀ k, m + k ≤ M →
      WN L (VortexCondense.rectWord L a b M n o) β
          (sheetAt L a b ((finRotate (L a)).symm (o a + (m : Fin (L a)))) pb)
        = WN L (VortexCondense.rectWord L a b M n o) β
          (sheetAt L a b ((finRotate (L a)).symm (o a + ((m + k : ℕ) : Fin (L a)))) pb) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      rw [ih (by omega)]
      set s : Fin (L a) := o a + ((m + k : ℕ) : Fin (L a)) with hs
      have hs1 : o a + ((m + (k + 1) : ℕ) : Fin (L a)) = s + 1 := by rw [hs]; push_cast; ring
      rw [hs1, symm_finRotate_add_one]
      refine WN_step L hab s pb _ β (count_zero L hab s pb M n o ?_ ?_)
      · intro e
        have h0 : ((m + k : ℕ) : Fin (L a)) = 0 := by rw [hs] at e; linear_combination e
        have := congrArg Fin.val h0
        rw [Fin.val_natCast, Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at this
        omega
      · intro e
        rw [iter_a, hs] at e
        have h0 : ((m + k : ℕ) : Fin (L a)) = (M : Fin (L a)) := by linear_combination e
        have := congrArg Fin.val h0
        rw [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : m + k < L a)] at this
        rcases Nat.lt_or_ge M (L a) with hlt | hge
        · rw [Nat.mod_eq_of_lt hlt] at this; omega
        · rw [show M = L a by omega, Nat.mod_self] at this; omega

theorem ev_move {a b : Fin 4} (hab : a ≠ b) [NeZero (L a)] (o : RSite L) (pb : Fin (L b))
    {m m' M : ℕ} (n : ℕ) (hm : 0 < m) (hmm : m ≤ m') (hmM : m' ≤ M) (hML : M ≤ L a) (β : ℝ) :
    ev L β (fun U => fluxOp L β (sheetAt L a b ((finRotate (L a)).symm (o a + (m : Fin (L a)))) pb) U
        * wObs L (VortexCondense.rectWord L a b M n o) U)
      = ev L β (fun U => fluxOp L β
          (sheetAt L a b ((finRotate (L a)).symm (o a + (m' : Fin (L a)))) pb) U
          * wObs L (VortexCondense.rectWord L a b M n o) U) := by
  obtain ⟨k, rfl⟩ : ∃ k, m' = m + k := ⟨m' - m, by omega⟩
  rw [ev_fluxOp_wObs, ev_fluxOp_wObs, WN_move L hab o pb n hm hML β k hmM]

/-- The rectangle read in the other orientation has the same Wilson observable. -/
theorem wObs_swap (a b : Fin 4) (M N : ℕ) (o : RSite L) :
    wObs L (VortexCondense.rectWord L a b M N o) = wObs L (VortexCondense.rectWord L b a N M o) := by
  funext U
  have e : wHol L (VortexCondense.rectWord L b a N M o) U
      = (wHol L (VortexCondense.rectWord L a b M N o) U)⁻¹ := by
    rw [rectHol_eq, rectHol_eq]
    group
  unfold wObs
  rw [e, wilsonDensity_inv]

/-- **The doubling iterated along `a`**: for `L_a = 2^p m` with `p ≥ 1`,
`|⟨F[sIn] W(m × n)⟩|^{2^p} ≤ ⟨F[sIn] W(L_a × n)⟩`, and the right side is `≥ 0`. -/
theorem chain_a {a b : Fin 4} (hab : a ≠ b) (o : RSite L) {m p : ℕ} (hm : 0 < m) (hp : 1 ≤ p)
    (hLp : L a = 2 ^ p * m) (n : ℕ) (β : ℝ) :
    |ev L β (fun U => fluxOp L β (sIn L a b m o) U
        * wObs L (VortexCondense.rectWord L a b m n o) U)| ^ (2 ^ p)
      ≤ ev L β (fun U => fluxOp L β (sIn L a b (L a) o) U
          * wObs L (VortexCondense.rectWord L a b (L a) n o) U)
    ∧ 0 ≤ ev L β (fun U => fluxOp L β (sIn L a b (L a) o) U
          * wObs L (VortexCondense.rectWord L a b (L a) n o) U) := by
  have hpos : 0 < L a := by rw [hLp]; positivity
  haveI : NeZero (L a) := ⟨hpos.ne'⟩
  set x : ℕ → ℝ := fun j => ev L β (fun U => fluxOp L β (sIn L a b (2 ^ j * m) o) U
    * wObs L (VortexCondense.rectWord L a b (2 ^ j * m) n o) U) with hx
  have hstep : ∀ j < p, x j ^ 2 ≤ x (j + 1) ∧ 0 ≤ x (j + 1) := by
    intro j hj
    have hh : L a = 2 * (2 ^ (p - 1) * m) := by
      rw [hLp, ← mul_assoc, ← pow_succ']; congr 2; omega
    have hjh : 2 ^ j * m ≤ 2 ^ (p - 1) * m :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hD := doubling L hab (2 ^ (p - 1) * m) hh o (by positivity) hjh n β
    have hmove : ev L β (fun U => fluxOp L β (sIn L a b (2 ^ j * m) o) U
        * wObs L (VortexCondense.rectWord L a b (2 * (2 ^ j * m)) n o) U) = x (j + 1) := by
      have e2 : 2 ^ (j + 1) * m = 2 * (2 ^ j * m) := by ring
      simp only [hx]
      rw [e2, sIn_eq, sIn_eq]
      exact ev_move L hab o (o b) n (by positivity) (by omega) le_rfl (by omega) β
    rw [hmove] at hD
    exact hD
  have hc := pow_chain x p hstep
  have hxp : 0 ≤ x p := by
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    exact (hstep k (by omega)).2
  have e0 : x 0 = ev L β (fun U => fluxOp L β (sIn L a b m o) U
      * wObs L (VortexCondense.rectWord L a b m n o) U) := by simp [hx]
  have ep : x p = ev L β (fun U => fluxOp L β (sIn L a b (L a) o) U
      * wObs L (VortexCondense.rectWord L a b (L a) n o) U) := by simp only [hx]; rw [← hLp]
  rw [← e0, ← ep]
  exact ⟨by rw [← abs_of_nonneg hxp]; exact hc, hxp⟩

/-- **The turn to the `(b, a)` orientation** for a rectangle of full `a`-width: the sheet slides to
`x_a = x_a(o)` and up to the far `b`-side, and the loop is read the other way round. -/
theorem turn {a b : Fin 4} (hab : a ≠ b) [NeZero (L a)] [NeZero (L b)] (o : RSite L) {n : ℕ}
    (hn : 0 < n) (hnL : n ≤ L b) (β : ℝ) :
    ev L β (fun U => fluxOp L β (sIn L a b (L a) o) U
        * wObs L (VortexCondense.rectWord L a b (L a) n o) U)
      = ev L β (fun U => fluxOp L β (sIn L b a n o) U
        * wObs L (VortexCondense.rectWord L b a n (L a) o) U) := by
  have hLa : 1 ≤ L a := Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
  rw [sIn_eq L a b (L a) o,
    ← ev_move L hab o (o b) n one_pos (m' := L a) (M := L a) hLa le_rfl le_rfl β, Nat.cast_one,
    symm_finRotate_add_one, sheetAt_symm L a b (o a) (o b), wObs_swap L a b (L a) n o,
    sIn_eq L b a n o,
    ← ev_move L (Ne.symm hab) o (o a) (L a) one_pos (m' := n) (M := n) hn le_rfl hnL β,
    Nat.cast_one, symm_finRotate_add_one]

/-- **The hypothesis-free chain of the inside half.** On an admissible rectangle with `L_a = 2^p m`
and `L_b = 2^q n`: `p` Schwarz doublings along `a`, the turn to the `(b, a)` orientation, and `q`
doublings along `b` give `|⟨F[sIn] W(m × n)⟩|^{2^{p+q}} ≤ ⟨F[sIn_{(b,a)}] W(L_b × L_a)⟩`. The right
side is the flux operator times the Wilson observable of the commutator `P_b P_a P_b⁻¹ P_a⁻¹` of the
two Polyakov lines at `o`. -/
theorem chain_full {a b : Fin 4} (hab : a ≠ b) (o : RSite L) {m n p q : ℕ}
    (hA : VortexCondense.Adm (L a) (L b) m n) (hp : L a = 2 ^ p * m) (hq : L b = 2 ^ q * n) (β : ℝ) :
    |ev L β (fun U => fluxOp L β (sIn L a b m o) U
        * wObs L (VortexCondense.rectWord L a b m n o) U)| ^ (2 ^ (p + q))
      ≤ ev L β (fun U => fluxOp L β (sIn L b a (L b) o) U
          * wObs L (VortexCondense.rectWord L b a (L b) (L a) o) U) := by
  obtain ⟨hm, hn⟩ := adm_pos hA
  obtain ⟨-, -, hmL, hnL⟩ := hA
  have hp1 : 1 ≤ p := by
    by_contra h0
    have : p = 0 := by omega
    rw [this, pow_zero, one_mul] at hp
    omega
  have hq1 : 1 ≤ q := by
    by_contra h0
    have : q = 0 := by omega
    rw [this, pow_zero, one_mul] at hq
    omega
  haveI : NeZero (L a) := ⟨by omega⟩
  haveI : NeZero (L b) := ⟨by omega⟩
  obtain ⟨hA1, hA2⟩ := chain_a L hab o hm hp1 hp n β
  obtain ⟨hB1, -⟩ := chain_a L (Ne.symm hab) o hn hq1 hq (L a) β
  rw [turn L hab o hn hnL.le β] at hA1 hA2
  generalize ev L β (fun U => fluxOp L β (sIn L a b m o) U
    * wObs L (VortexCondense.rectWord L a b m n o) U) = x0 at hA1 ⊢
  generalize ev L β (fun U => fluxOp L β (sIn L b a n o) U
    * wObs L (VortexCondense.rectWord L b a n (L a) o) U) = y0 at hA1 hA2 hB1
  calc |x0| ^ (2 ^ (p + q)) = (|x0| ^ (2 ^ p)) ^ (2 ^ q) := by rw [pow_add, pow_mul]
    _ ≤ y0 ^ (2 ^ q) := pow_le_pow_left₀ (by positivity) hA1 _
    _ = |y0| ^ (2 ^ q) := by rw [abs_of_nonneg hA2]
    _ ≤ _ := hB1

/-- `⟨F W_w⟩ = ⟨F⟩ − ⟨F · wd(U[w])⟩`, from `W_w = 1 − wd(U[w])`. -/
theorem ev_fluxOp_wObs_split (w : List (RLink L × Bool)) (β : ℝ) (ζ : RPlaq L → SUN.SU 2) :
    ev L β (fun U => fluxOp L β ζ U * wObs L w U)
      = ev L β (fluxOp L β ζ) - ev L β (fun U => fluxOp L β ζ U * wd (wHol L w U)) := by
  have hZ := (ZRp_pos L β (fun _ => 1)).ne'
  have h1 := int_eq_ev L β (fun U => fluxOp L β ζ U * wObs L w U)
  have h2 := int_eq_ev L β (fluxOp L β ζ)
  have h3 := int_eq_ev L β (fun U => fluxOp L β ζ U * wd (wHol L w U))
  have hF := continuous_fluxOp L β ζ
  have hW : Continuous fun U : RLink L → SUN.SU 2 => wd (wHol L w U) :=
    WilsonAction.continuous_wilsonDensity.comp (continuous_wHol L w)
  have hi : ∫ U, fluxOp L β ζ U * wObs L w U * E L β U
        ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))
      = ∫ U, fluxOp L β ζ U * E L β U ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))
        - ∫ U, fluxOp L β ζ U * wd (wHol L w U) * E L β U
          ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)) := by
    rw [← integral_sub
      (integrable_of_continuous (f := fun U => fluxOp L β ζ U * E L β U) (hF.mul (continuous_E L β)))
      (integrable_of_continuous (f := fun U => fluxOp L β ζ U * wd (wHol L w U) * E L β U)
        ((hF.mul hW).mul (continuous_E L β)))]
    congr 1
    funext U
    unfold wObs
    ring
  try simp only at h1 h3
  rw [h1, h2, h3, ← sub_mul] at hi
  exact mul_right_cancel₀ hZ hi

/-- **The remaining input of the inside half**: the flux operator of the sheet times the Wilson
observable of the loop that runs once around the whole `(b, a)` torus (`L_b × L_a`) is at most the
flux `(1 − zR)/2` of a single sheet. On the lattice that loop has holonomy `P_b P_a P_b⁻¹ P_a⁻¹`, the
commutator of the two Polyakov lines at `o`, not the identity. By `fullLoopFlux_iff` this is
`0 ≤ ⟨F[sIn_{(b,a)}] · wd(P_b P_a P_b⁻¹ P_a⁻¹)⟩`; `fluxOp` is not pointwise nonnegative (`vortexOp`
ranges over `[e^{−2β|S|}, e^{2β|S|}]`), so this does not follow from `wd ≥ 0`.

This input is not known to hold, and it fails in some geometries. In the exact two-dimensional
analogue `Z · ⟨F · wd(W_full)⟩ = −Σ_{j half-integer} c_j^N/(d_j² − 1) < 0` at every `β ≠ 0`, so the
analogue of `FullLoopFlux` fails there. In four dimensions the leading small-`β` term of
`Z · ⟨F · wd(W_full)⟩` is `u^N (9K − 13)/12` with `K = L_c L_d` the transverse area; for `K = 1`
(e.g. `L = (2, 2, 1, 1)`, `N` even) it is negative, so `FullLoopFlux` is false at small `β > 0`. This
is a leading-order computation and is not machine-checked here. For `K ≥ 2` it is open. This is the
gap in Kanazawa, arXiv:0808.3442, eq. (40), where "the rectangle finally vanishes away" sets the
full-torus loop to `1`; on the lattice it is the commutator.

DERIVED: the definition carries no numeral but `1` and `2` (the unit and the halving of the flux);
`0808.3442` and `40` are the arXiv identifier and equation number cited; `9`, `12`, `13` the
coefficients of the leading small-`β` term, a hand computation not machine-checked here. -/
def FullLoopFlux (a b : Fin 4) (o : RSite L) (β : ℝ) : Prop :=
  ev L β (fun U => fluxOp L β (sIn L b a (L b) o) U
      * wObs L (VortexCondense.rectWord L b a (L b) (L a) o) U) ≤ (1 - zR L a b β) / 2

/-- **`FullLoopFlux` as a sign condition**: it holds iff
`0 ≤ ⟨F[sIn_{(b,a)}] · wd(U[W(L_b × L_a)])⟩`, with `U[W(L_b × L_a)] = P_b P_a P_b⁻¹ P_a⁻¹`. -/
theorem fullLoopFlux_iff {a b : Fin 4} (hab : a ≠ b) (o : RSite L) (β : ℝ) :
    FullLoopFlux L a b o β ↔
      0 ≤ ev L β (fun U => fluxOp L β (sIn L b a (L b) o) U
        * wd (wHol L (VortexCondense.rectWord L b a (L b) (L a) o) U)) := by
  have hf : ev L β (fluxOp L β (sIn L b a (L b) o)) = (1 - zR L a b β) / 2 := by
    rw [sIn, sheetAt_symm, ev_fluxOp_sheet L hab]
  unfold FullLoopFlux
  rw [ev_fluxOp_wObs_split, hf]
  constructor <;> intro h <;> linarith

/-- **The inside half of the chessboard estimate, conditional on `FullLoopFlux`.** On every `AdmTwo`
rectangle, `⟨F[sIn] W(C)⟩ ≤ ⟨F[sIn]⟩^{mn/(L_a L_b)}`, given `FullLoopFlux`, which is not known to
hold and fails in some geometries (see `FullLoopFlux`). The proof is `chain_full` followed by
`FullLoopFlux`. -/
theorem chessboard_in {a b : Fin 4} (hab : a ≠ b) (o : RSite L) {β : ℝ}
    (hF : FullLoopFlux L a b o β) {m n : ℕ} (hadm : AdmTwo (L a) (L b) m n) :
    ev L β (fun U => fluxOp L β (sIn L a b m o) U * wObs L (VortexCondense.rectWord L a b m n o) U)
      ≤ ev L β (fluxOp L β (sIn L a b m o)) ^ (((m : ℝ) * n) / ((L a : ℝ) * L b)) := by
  obtain ⟨hA, ⟨p, hp⟩, ⟨q, hq⟩⟩ := hadm
  obtain ⟨hm, hn⟩ := adm_pos hA
  have hC := chain_full L hab o hA hp hq β
  have hf : ev L β (fluxOp L β (sIn L a b m o)) = (1 - zR L a b β) / 2 := by
    rw [sIn, ev_fluxOp_sheet L hab]
  rw [hf]
  unfold FullLoopFlux at hF
  generalize ev L β (fun U => fluxOp L β (sIn L a b m o) U
    * wObs L (VortexCondense.rectWord L a b m n o) U) = x0 at hC ⊢
  generalize ev L β (fun U => fluxOp L β (sIn L b a (L b) o) U
    * wObs L (VortexCondense.rectWord L b a (L b) (L a) o) U) = yB at hC hF
  generalize (1 - zR L a b β) / 2 = f at hF ⊢
  have hN : |x0| ^ (2 ^ (p + q)) ≤ f := hC.trans hF
  have hexp : ((m : ℝ) * n) / ((L a : ℝ) * L b) = (((2 ^ (p + q) : ℕ) : ℝ))⁻¹ := by
    rw [hp, hq]
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    push_cast
    field_simp
    ring
  rw [hexp]
  have hN0 : (2 ^ (p + q) : ℕ) ≠ 0 := by positivity
  calc x0 ≤ |x0| := le_abs_self _
    _ = (|x0| ^ (2 ^ (p + q))) ^ (((2 ^ (p + q) : ℕ) : ℝ))⁻¹ :=
        (Real.pow_rpow_inv_natCast (abs_nonneg _) hN0).symm
    _ ≤ f ^ (((2 ^ (p + q) : ℕ) : ℝ))⁻¹ :=
        Real.rpow_le_rpow (by positivity) hN (by positivity)

/-- The outside half of `ChessboardFlux`, as stated there. -/
def OutsideFlux (a b : Fin 4) (o : RSite L) (β : ℝ) : Prop :=
  ∀ m n, AdmTwo (L a) (L b) m n →
    ev L β (fun U => fluxOp L β (sOut L a b m o) U * wObs L (VortexCondense.rectWord L a b m n o) U)
      ≤ ev L β (fluxOp L β (sOut L a b m o)) ^ (((m : ℝ) * n) / ((L a : ℝ) * L b))

/-- **`ChessboardFlux`, conditional on two inputs**: `FullLoopFlux` (the last step of the inside
half) and `OutsideFlux` (the outside half). Neither is proved; `FullLoopFlux` is not known to hold and
fails in some geometries (see `FullLoopFlux`). -/
theorem chessboardFlux_of {a b : Fin 4} (hab : a ≠ b) (o : RSite L) {β : ℝ}
    (hF : FullLoopFlux L a b o β) (hO : OutsideFlux L a b o β) : ChessboardFlux L a b o β :=
  fun m n hadm => ⟨chessboard_in L hab o hF hadm, hO m n hadm⟩

end Chain

#print axioms pow_chain
#print axioms WN_move
#print axioms wObs_swap
#print axioms chain_a
#print axioms chain_full
#print axioms ev_fluxOp_wObs_split
#print axioms fullLoopFlux_iff
#print axioms chessboard_in
#print axioms chessboardFlux_of
#print axioms doubling
#print axioms int_flux2_wObs
#print axioms count_zero
#print axioms sheet_rp
#print axioms vortexOp_reads
#print axioms sumX
#print axioms rectHol_eq
#print axioms pathA_Θ

#print axioms sq_le_of_quad
#print axioms wd_refl
#print axioms E_Θ
#print axioms action_split
#print axioms rp_nonneg
#print axioms bil_symm
#print axioms bil_sq_le

end MassGap.Chessboard
