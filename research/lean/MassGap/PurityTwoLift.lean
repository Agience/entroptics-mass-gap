import Mathlib
import MassGap.PurityMomentMatch

/-!
# MassGap.PurityTwoLift — moment matching on the double cover of a cycle

The moment matching behind (8.1) of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood,
T. Romanov, I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak
Coupling* (research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>,
commit 8e01510, `Paper-2/Paper-2.pdf`), for a nearest-neighbour chain.

Sites are `x : Fin (m+1)`, each carrying two variables `Z x : E × E` (sheets `false`, `true`)
drawn i.i.d. from `μ`. For a bond weight `b : E → E → ℝ`:

* `chain b Y = Σ_x b(Y x, Y (x+1))`, the cycle of circumference `T = m+1`;
* `cover b Z = Σ_{(x,e)} b(Z_x^e, Z_{x+1}^{e ⊕ flip x})`, `flip x = (x = last)`: the connected
  double cover, the cycle of circumference `2T`;
* `trivialCover b Z = Σ_{(x,e)} b(Z_x^e, Z_{x+1}^e) = chain b Z^false + chain b Z^true`
  (`trivialCover_eq`), two independent cycles of circumference `T`.

`moment_cover`: for `n < T`,
`E[cover^n] = Σ_{i ≤ n} C(n,i) E[chain^i] E[chain^{n−i}]`.

Proof. `cover^n` and `trivialCover^n` expand over bond tuples `f : Fin n → Fin (m+1) × Bool`.
A tuple with `n < T` entries misses the bond based at some site `j` (`exists_missing`). Cutting
both covers at the fibre over `j` identifies them: the sheet relabelling
`cut j (x,e) = (x, e ⊕ [x ≤ j])` carries every cover bond off that fibre to a trivial-cover bond
(`bond_cut`), and the matching site map `swapLe j` (swap the two sheets at `x ≤ j`) preserves the
product measure. `lift f = cut (jOf (Prod.fst ∘ f)) ∘ f` keeps the base projection, hence the missing bond, so it is an involution on tuples (`lift_lift`), and
the tuple sums agree term by term after reindexing (`moment_cover_eq_trivial`). The trivial-cover
moments split by independence and the binomial theorem (`moment_trivial`).

`hvan_cover`: the hypothesis `hvan` of `PurityCancel.corollary_window` for `A_T = chain b`,
`A_{2T} = cover b`, through `PurityMomentMatch.hvan_of_moments`.
-/

namespace MassGap.PurityTwoLift

open MeasureTheory

variable {E : Type*} {m : ℕ}

/-- The variable on sheet `e`. -/
def get (p : E × E) (e : Bool) : E := if e then p.2 else p.1

/-- The sheet changes on the bond from `last` to `0`. -/
def flip (x : Fin (m + 1)) : Bool := decide (x = Fin.last m)

/-- The cycle of circumference `m+1`. -/
def chain (b : E → E → ℝ) (Y : Fin (m + 1) → E) : ℝ := ∑ x, b (Y x) (Y (x + 1))

/-- A bond of the connected double cover. -/
def coverBond (b : E → E → ℝ) (Z : Fin (m + 1) → E × E) (s : Fin (m + 1) × Bool) : ℝ :=
  b (get (Z s.1) s.2) (get (Z (s.1 + 1)) (xor s.2 (flip s.1)))

/-- A bond of the trivial double cover. -/
def trivialBond (b : E → E → ℝ) (Z : Fin (m + 1) → E × E) (s : Fin (m + 1) × Bool) : ℝ :=
  b (get (Z s.1) s.2) (get (Z (s.1 + 1)) s.2)

/-- The connected double cover: the cycle of circumference `2(m+1)`. -/
def cover (b : E → E → ℝ) (Z : Fin (m + 1) → E × E) : ℝ := ∑ s, coverBond b Z s

/-- The trivial double cover: two cycles of circumference `m+1`. -/
def trivialCover (b : E → E → ℝ) (Z : Fin (m + 1) → E × E) : ℝ := ∑ s, trivialBond b Z s

theorem trivialCover_eq (b : E → E → ℝ) (Z : Fin (m + 1) → E × E) :
    trivialCover b Z = chain b (fun x => (Z x).1) + chain b (fun x => (Z x).2) := by
  rw [trivialCover, chain, chain, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [trivialBond, get, add_comm]

/-- Relabel the sheets on the base sites `x ≤ j`. -/
def cut (j : Fin (m + 1)) (s : Fin (m + 1) × Bool) : Fin (m + 1) × Bool :=
  (s.1, xor s.2 (decide (s.1 ≤ j)))

/-- Swap the two sheets on the base sites `x ≤ j`. -/
def swapLe (j : Fin (m + 1)) (Z : Fin (m + 1) → E × E) : Fin (m + 1) → E × E :=
  fun x => if x ≤ j then (Z x).swap else Z x

theorem get_swapLe (j : Fin (m + 1)) (Z : Fin (m + 1) → E × E) (x : Fin (m + 1)) (e : Bool) :
    get (swapLe j Z x) e = get (Z x) (xor e (decide (x ≤ j))) := by
  unfold swapLe get
  by_cases h : x ≤ j <;> cases e <;> simp [h]

/-- Off the fibre over `j`, the sheet relabelling carries cover bonds to trivial-cover bonds. -/
theorem bond_cut (b : E → E → ℝ) (Z : Fin (m + 1) → E × E) {j : Fin (m + 1)}
    (s : Fin (m + 1) × Bool) (hs : s.1 ≠ j) :
    trivialBond b (swapLe j Z) (cut j s) = coverBond b Z s := by
  obtain ⟨x, e⟩ := s
  simp only at hs
  have key : xor (decide (x ≤ j)) (decide (x + 1 ≤ j)) = flip x := by
    unfold flip
    by_cases hx : x = Fin.last m
    · subst hx
      have h1 : ¬ Fin.last m ≤ j := fun h => hs (le_antisymm (Fin.le_last j) h).symm
      have h0 : (Fin.last m + 1 : Fin (m + 1)) = 0 := Fin.last_add_one m
      simp [h1, h0]
    · have hv : ((x + 1 : Fin (m + 1)) : ℕ) = x + 1 := by
        rw [Fin.val_add_one]; simp [hx]
      have : (x ≤ j) ↔ (x + 1 ≤ j) := by
        rw [Fin.le_iff_val_le_val, Fin.le_iff_val_le_val, hv]
        have : (x : ℕ) ≠ j := fun h => hs (Fin.ext h)
        omega
      simp [this, hx]
  unfold trivialBond coverBond cut
  simp only
  rw [get_swapLe, get_swapLe, Bool.xor_assoc, Bool.xor_self, Bool.xor_false, Bool.xor_assoc, key]

/-- A tuple of fewer than `m+1` bonds misses the bond based at some site. -/
theorem exists_missing {n : ℕ} (hn : n < m + 1) (g : Fin n → Fin (m + 1)) :
    ∃ j, ∀ i, g i ≠ j := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin (m + 1))) ⊆ Finset.univ.image g := fun j _ => by
    obtain ⟨i, hi⟩ := h j
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  simp at this
  omega

/-- A base site missed by `g` (`0` when there is none). -/
noncomputable def jOf {n : ℕ} (g : Fin n → Fin (m + 1)) : Fin (m + 1) := by
  classical
  exact if h : ∃ j, ∀ i, g i ≠ j then h.choose else 0

theorem jOf_spec {n : ℕ} (hn : n < m + 1) (g : Fin n → Fin (m + 1)) (i : Fin n) :
    g i ≠ jOf g := by
  have h := exists_missing hn g
  unfold jOf
  rw [dif_pos h]
  exact h.choose_spec i

/-- Relabel a bond tuple at its missing base site. -/
noncomputable def lift {n : ℕ} (f : Fin n → Fin (m + 1) × Bool) : Fin n → Fin (m + 1) × Bool :=
  fun i => cut (jOf fun k => (f k).1) (f i)

theorem cut_cut (j : Fin (m + 1)) (s : Fin (m + 1) × Bool) : cut j (cut j s) = s := by
  obtain ⟨x, e⟩ := s
  unfold cut
  cases decide (x ≤ j) <;> cases e <;> rfl

theorem lift_lift {n : ℕ} (f : Fin n → Fin (m + 1) × Bool) : lift (lift f) = f :=
  funext fun i => cut_cut (jOf fun k => (f k).1) (f i)

variable [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]

theorem measurable_get (x : Fin (m + 1)) (e : Bool) :
    Measurable fun Z : Fin (m + 1) → E × E => get (Z x) e := by
  cases e
  · exact measurable_fst.comp (measurable_pi_apply x)
  · exact measurable_snd.comp (measurable_pi_apply x)

theorem measurePreserving_swapLe (j : Fin (m + 1)) :
    MeasurePreserving (swapLe (E := E) j) (Measure.pi fun _ => μ.prod μ)
      (Measure.pi fun _ => μ.prod μ) := by
  have := measurePreserving_pi (fun _ : Fin (m + 1) => μ.prod μ) (fun _ => μ.prod μ)
    (f := fun x (p : E × E) => if x ≤ j then p.swap else p) fun x => by
      by_cases h : x ≤ j
      · simp only [h, if_true]; exact Measure.measurePreserving_swap
      · simp only [h, if_false]; exact MeasurePreserving.id _
  convert this using 1
  funext Z x
  unfold swapLe
  split_ifs <;> rfl

variable {b : E → E → ℝ} (hb : Measurable (Function.uncurry b)) {C : ℝ} (hC : ∀ x y, |b x y| ≤ C)
include hb hC

omit hC in
theorem measurable_prod_bonds (B : (Fin (m + 1) → E × E) → Fin (m + 1) × Bool → ℝ)
    (hB : B = coverBond b ∨ B = trivialBond b) {n : ℕ} (f : Fin n → Fin (m + 1) × Bool) :
    Measurable fun Z => ∏ i, B Z (f i) := by
  refine Finset.measurable_prod _ fun i _ => ?_
  rcases hB with rfl | rfl
  · exact hb.comp ((measurable_get _ _).prodMk (measurable_get _ _))
  · exact hb.comp ((measurable_get _ _).prodMk (measurable_get _ _))

theorem integrable_prod_bonds (B : (Fin (m + 1) → E × E) → Fin (m + 1) × Bool → ℝ)
    (hB : B = coverBond b ∨ B = trivialBond b) {n : ℕ} (f : Fin n → Fin (m + 1) × Bool) :
    Integrable (fun Z => ∏ i, B Z (f i)) (Measure.pi fun _ => μ.prod μ) := by
  refine Integrable.of_bound (measurable_prod_bonds hb B hB f).aestronglyMeasurable (C ^ n)
    (ae_of_all _ fun Z => ?_)
  rw [Real.norm_eq_abs, Finset.abs_prod]
  calc ∏ i, |B Z (f i)| ≤ ∏ _i : Fin n, C :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => by
          rcases hB with rfl | rfl
          · exact hC _ _
          · exact hC _ _
    _ = C ^ n := by simp

/-- `X^n` of a bond sum, integrated, as a sum over bond tuples. -/
theorem integral_pow_eq (B : (Fin (m + 1) → E × E) → Fin (m + 1) × Bool → ℝ)
    (hB : B = coverBond b ∨ B = trivialBond b) (n : ℕ) :
    ∫ Z, (∑ s, B Z s) ^ n ∂(Measure.pi fun _ => μ.prod μ)
      = ∑ f : Fin n → Fin (m + 1) × Bool, ∫ Z, ∏ i, B Z (f i) ∂(Measure.pi fun _ => μ.prod μ) := by
  rw [← integral_finsetSum _ fun f _ => integrable_prod_bonds μ hb hC B hB f]
  refine integral_congr_ae (ae_of_all _ fun Z => ?_)
  simp only
  rw [← Fin.prod_const n (∑ s, B Z s), Fintype.prod_sum]

/-- For `n < m+1`, the moments of the connected cover equal those of the trivial cover. -/
theorem moment_cover_eq_trivial {n : ℕ} (hn : n < m + 1) :
    ∫ Z : Fin (m + 1) → E × E, cover b Z ^ n ∂(Measure.pi fun _ => μ.prod μ)
      = ∫ Z : Fin (m + 1) → E × E, trivialCover b Z ^ n ∂(Measure.pi fun _ => μ.prod μ) := by
  unfold cover trivialCover
  rw [integral_pow_eq μ hb hC _ (Or.inl rfl), integral_pow_eq μ hb hC _ (Or.inr rfl)]
  have hinv : Function.Involutive (lift (m := m) (n := n)) := lift_lift
  refine Fintype.sum_equiv (hinv.toPerm _) _ _ fun f => ?_
  rw [Function.Involutive.coe_toPerm]
  have hmp := measurePreserving_swapLe μ (jOf fun k => (f k).1) (E := E)
  have h2 := integral_map
    (hmp.measurable.aemeasurable (μ := Measure.pi fun _ : Fin (m + 1) => μ.prod μ))
    (measurable_prod_bonds hb _ (Or.inr rfl) (lift f)).aestronglyMeasurable
  rw [hmp.map_eq] at h2
  rw [h2]
  refine integral_congr_ae (ae_of_all _ fun Z => ?_)
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (bond_cut b Z (f i) (jOf_spec hn (fun k => (f k).1) i)).symm

omit hb hC in
theorem measurable_chain (hb : Measurable (Function.uncurry b)) :
    Measurable (chain (m := m) b) :=
  Finset.measurable_sum _ fun x _ =>
    hb.comp (f := fun Y : Fin (m + 1) → E => (Y x, Y (x + 1)))
      ((measurable_pi_apply x).prodMk (measurable_pi_apply (x + 1)))

omit [MeasurableSpace E] hb in
theorem abs_chain_le (Y : Fin (m + 1) → E) : |chain b Y| ≤ (m + 1) * C := by
  unfold chain
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ x, |b (Y x) (Y (x + 1))| ≤ ∑ _x : Fin (m + 1), C :=
        Finset.sum_le_sum fun x _ => hC _ _
    _ = (m + 1) * C := by simp

theorem integrable_chain_pow (k : ℕ) :
    Integrable (fun Y => chain (m := m) b Y ^ k) (Measure.pi fun _ => μ) := by
  refine Integrable.of_bound ((measurable_chain hb).pow_const k).aestronglyMeasurable
    (((m + 1) * C) ^ k) (ae_of_all _ fun Y => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_chain_le hC Y) k

/-- The moments of the trivial cover: two independent cycles. -/
theorem moment_trivial (n : ℕ) :
    ∫ Z : Fin (m + 1) → E × E, trivialCover b Z ^ n ∂(Measure.pi fun _ => μ.prod μ)
      = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * (∫ Y, chain (m := m) b Y ^ i ∂(Measure.pi fun _ => μ))
          * ∫ Y, chain (m := m) b Y ^ (n - i) ∂(Measure.pi fun _ => μ) := by
  have hmp := measurePreserving_arrowProdEquivProdArrow E E (Fin (m + 1))
    (fun _ => μ) (fun _ => μ)
  let G : (Fin (m + 1) → E) × (Fin (m + 1) → E) → ℝ := fun p => (chain b p.1 + chain b p.2) ^ n
  have hF : (fun Z => trivialCover b Z ^ n)
      = fun Z => G (MeasurableEquiv.arrowProdEquivProdArrow E E (Fin (m + 1)) Z) :=
    funext fun Z => by simp only [G]; rw [trivialCover_eq]; rfl
  rw [hF, hmp.integral_comp' G]
  simp only [G, add_pow]
  rw [integral_finsetSum _ fun i _ =>
    ((integrable_chain_pow μ hb hC i).mul_prod (integrable_chain_pow μ hb hC (n - i))).mul_const _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_mul_const, integral_prod_mul (f := fun Y => chain b Y ^ i)
    (g := fun Y => chain b Y ^ (n - i))]
  ring

/-- For `n < m+1`: `E[cover^n] = Σ_{i ≤ n} C(n,i) E[chain^i] E[chain^{n−i}]`. -/
theorem moment_cover {n : ℕ} (hn : n < m + 1) :
    ∫ Z : Fin (m + 1) → E × E, cover b Z ^ n ∂(Measure.pi fun _ => μ.prod μ)
      = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * (∫ Y, chain (m := m) b Y ^ i ∂(Measure.pi fun _ => μ))
          * ∫ Y, chain (m := m) b Y ^ (n - i) ∂(Measure.pi fun _ => μ) := by
  rw [moment_cover_eq_trivial μ hb hC hn, moment_trivial μ hb hC]

omit hC in
theorem measurable_cover : Measurable (cover (m := m) b) := by
  unfold cover
  exact Finset.measurable_sum _ fun s _ =>
    hb.comp ((measurable_get _ _).prodMk (measurable_get _ _))

omit [MeasurableSpace E] hb in
theorem abs_cover_le (Z : Fin (m + 1) → E × E) : |cover b Z| ≤ 2 * (m + 1) * C := by
  unfold cover
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ s, |coverBond b Z s| ≤ ∑ _s : Fin (m + 1) × Bool, C :=
        Finset.sum_le_sum fun s _ => hC _ _
    _ = 2 * (m + 1) * C := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring

/-- (8.1) for the cycle: the derivatives of `2 log Z_T − log Z_{2T}` of order `< T` vanish at `0`,
`A_T = chain b`, `A_{2T} = cover b`. -/
theorem hvan_cover : ∀ n < m + 1, iteratedDeriv n (PurityCancel.psi
    (Measure.pi fun _ : Fin (m + 1) => μ) (chain b)
    (Measure.pi fun _ : Fin (m + 1) => μ.prod μ) (cover b)) 0 = 0 :=
  PurityMomentMatch.hvan_of_moments (measurable_chain hb).aemeasurable
    (ae_of_all _ (abs_chain_le hC)) (measurable_cover hb).aemeasurable
    (ae_of_all _ (abs_cover_le hC)) fun n hn => by
      simp only [← Complex.ofReal_pow, integral_complex_ofReal]
      rw [moment_cover μ hb hC hn]
      push_cast
      rfl

end MassGap.PurityTwoLift

#print axioms MassGap.PurityTwoLift.bond_cut
#print axioms MassGap.PurityTwoLift.moment_cover_eq_trivial
#print axioms MassGap.PurityTwoLift.moment_trivial
#print axioms MassGap.PurityTwoLift.moment_cover
#print axioms MassGap.PurityTwoLift.hvan_cover
