import Mathlib
import MassGap.StripTail
import MassGap.StripGas

/-!
# MassGap.StripNest — separated rectangles off the seam of the 2D torus are independent, up to the exterior

`StripTail.plane_forget` compares a function of one rectangle with the free rectangle. This module proves the form for many
rectangles: functions of separated rectangles are independent under the 2D torus measure, up to a relative error in the
exterior area, and with no gauge invariance. Declarations are in `MassGap.StripNest`.

## The result

`Rc n`: a rectangle of faces of the side-`n` torus, not touching the seam of coordinates. `Sep`: the rectangles and their rings
are disjoint from the other rectangles. Two unit squares at offsets `1` and `4` on the side-`8` torus should be an instance (not formalized). For `R i`, `i ∈ T`, separated, `E = outT R T` the exterior, `e = |E|`:

* `conn_outT`: the exterior is connected, by induction on the rectangles: a rectangle put back is joined through its ring.
* `exits2_of_conn`, `integral_mul_prod_peel2`, `forget_eq2`, `forget_bounds2`: the peel of `StripTail`, along an undirected
  connection and any free link of a face.
* `multi_forget`: for `G_i ≥ 0` continuous, reading the links of `R i` only, with `m = b^e − c^e`, `δ = (1 − e^{−4β})^e`,
  `W_i = ∏_{R i} wt`: `m ∏_i ∫ G_i W_i ≤ ∫ ∏_i G_i ∏_x wt` and `(1 − δ) ∫ ∏_i G_i ∏_x wt ≤ m ∏_i ∫ G_i W_i`.
* `multi_mean`: for `e ≠ 0`, `(1 − δ) ∏_i μ_i(G_i) ≤ ⟨∏_i G_i⟩ ≤ ∏_i μ_i(G_i)/(1 − δ)`, `μ_i(G) = ∫ G W_i/∫ W_i`, `⟨·⟩` the
  Wilson torus expectation.

## The second layer, on paper

Argued, not proved.

* The conditional ratio at `U(1)`. Plaquette angles i.i.d. with variance `σ² = 1/β` (Villain), a disc of area `A`, a density
  perturbed by `1 + g`. Then `Φ(L) = p̃^{*A}(L)/p^{*A}(L)` for the normalized tilted density `p̃`. For `g` with `|g''| ≤ Λ` on the
  scale `1`, `log Φ(L) ≈ A (⟨g⟩_{L/A} − ⟨g⟩_0) ≈ Λ L²/(2A)`, with the theta-function form below the wrap scale and
  `Φ → 1` for `A ≫ β`. So `|log Φ| ≤ C Λ`, uniformly in `β`, with no factor of the perimeter.
* For `g` bounded by `Λ` in sup only, this is false. For `g = Λ h(θ √β)`, on the scale `σ`, the relative variance moves by `Λ`,
  and `log Φ(L) ≈ Λ β L²/A` while `A ≫ L √β`, of order `Λ √β` at `A ≈ √β`, against the perimeter `β^{1/4}`. A perimeter bound for
  every local class function of sup size `Λ` is false. Needed in addition: two derivatives on the scale `1`, which `y_x` is expected to have.
* The conditioning needs a pointwise ratio of convolution powers at all areas `1 ≤ A ≲ β`, large deviations included. At `SU(N)` that is
  a local limit estimate on the group, not in this tree.
* At `U(1)` the contour form is not needed: the face angles are i.i.d. and the layer has small influence in them, a
  Dobrushin condition uniform in `β`. At `SU(N)` faces in a common axial frame are i.i.d., but a local non-face loop reads the frame `A`
  in `A P A⁻¹ P'`, a column product of far faces, so that influence is not small. That is where the groups differ on this route.

## What does not follow

* The perimeter bound of the coordinator's plan, `|log Φ(L)| ≤ C m Λ` for tilts bounded by `Λ` in sup, is false (argued above at `U(1)`).
  The corrected form asks the same bound for tilts with two derivatives bounded by `Λ` on scale `1`. Its two inputs are not proved:
  regularity of `StripOsc.yS` on scale `1`, and a pointwise ratio of convolution powers for all `1 ≤ A ≲ β`, which at `SU(N)` is a
  local limit theorem on the group.
* The constant-width strip is not proved, and `t = β` is not reached.
* `boxM` is the free-rectangle mean on the side-`n` torus, through `μL n N`; it is not the `n`-independent `StripTail.planeMean`.
* `multi_forget` allows `e = 0`, where `m = 0` and the statement is empty; `multi_mean` assumes `e ≠ 0`. At `β = 0`, `δ = 0` and the
  bounds of `multi_mean` are equalities.

* The missing inequality of `StripTail` stays open, and so does `E_n[exp Σ_x yS]` at `t > 0`: `multi_forget` needs `G` to read
  rectangle links only.
* `δ` is in the exterior area with the rate `fl`. A family filling the plane has small `e`. The rectangles are not allowed on the seam.
* Rectangles are not read across sides: `∫ G_i W_i` on sides `n`, `n'` is compared only at the origin, by `StripTail.plane_compare`.
* A nested pair is not covered: `Sep` forbids it, and that is the case of the contour form.

DERIVED (module-wide): `0`, `1` the two directions and the seam; `2` the least side; `4` the links of a face. Inherited: `e^{−4β}` of
`TwoDVanish.fl`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.StripNest

open MeasureTheory Filter Topology MassGap MassGap.TorusDoubling MassGap.TwoDVanish MassGap.StripTail
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)
open MassGap.WilsonAction (wilsonDensity)

variable {N n : ℕ}

/-! ## 1. Links and adjacency -/

/-- The links of a face. DERIVED: `4` the links. -/
def links (f : TSite 2 n) : Finset (TLink 2 n) := {(0, f), (1, tshift 0 f), (0, tshift 1 f), (1, f)}

theorem mem_links {ℓ : TLink 2 n} {f : TSite 2 n} :
    ℓ ∈ links f ↔ ℓ = (0, f) ∨ ℓ = (1, tshift 0 f) ∨ ℓ = (0, tshift 1 f) ∨ ℓ = (1, f) := by
  simp [links]

/-- Faces with a common link. No numeral. -/
def Adj (f g : TSite 2 n) : Prop := ∃ i : Fin 2, tshift i f = g ∨ tshift i g = f

theorem adj_symm {f g : TSite 2 n} (h : Adj f g) : Adj g f := by
  obtain ⟨i, h⟩ := h
  exact ⟨i, h.symm⟩

/-- **Faces with a common link are equal or adjacent.** No numeral. -/
theorem link_shared {ℓ : TLink 2 n} {f g : TSite 2 n} (h1 : ℓ ∈ links f) (h2 : ℓ ∈ links g) :
    f = g ∨ Adj f g := by
  rw [mem_links] at h1 h2
  rcases h1 with rfl | rfl | rfl | rfl <;> rcases h2 with h | h | h | h <;>
    first
    | exact Or.inl (congrArg Prod.snd h)
    | exact Or.inl (tshift_injective _ (congrArg Prod.snd h))
    | exact Or.inr ⟨0, Or.inl (congrArg Prod.snd h)⟩
    | exact Or.inr ⟨1, Or.inl (congrArg Prod.snd h)⟩
    | exact Or.inr ⟨0, Or.inr (congrArg Prod.snd h).symm⟩
    | exact Or.inr ⟨1, Or.inr (congrArg Prod.snd h).symm⟩
    | exact absurd (show (0 : Fin 2) = 1 from congrArg Prod.fst h) (by decide)
    | exact absurd (show (1 : Fin 2) = 0 from congrArg Prod.fst h) (by decide)

/-- **An adjacent pair shares a link of those two faces only.** No numeral. -/
theorem side_faces {f g : TSite 2 n} (h : Adj f g) :
    ∃ ℓ, ℓ ∈ links f ∧ ℓ ∈ links g ∧ ∀ x, ℓ ∈ links x → x = f ∨ x = g := by
  have key : ∀ {a b : TSite 2 n} (i : Fin 2), tshift i a = b →
      ∃ ℓ, ℓ ∈ links a ∧ ℓ ∈ links b ∧ ∀ x, ℓ ∈ links x → x = a ∨ x = b := by
    intro a b i hab
    fin_cases i
    · have hab' : tshift 0 a = b := hab
      refine ⟨(1, b), mem_links.2 (Or.inr (Or.inl (by rw [hab']))), mem_links.2 (Or.inr (Or.inr (Or.inr rfl))),
        fun x hx => ?_⟩
      rw [mem_links] at hx
      rcases hx with h | h | h | h
      · exact absurd (congrArg Prod.fst h) (by simp)
      · refine Or.inl (tshift_injective 0 ?_)
        rw [hab']
        exact (congrArg Prod.snd h).symm
      · exact absurd (congrArg Prod.fst h) (by simp)
      · exact Or.inr (congrArg Prod.snd h).symm
    · have hab' : tshift 1 a = b := hab
      refine ⟨(0, b), mem_links.2 (Or.inr (Or.inr (Or.inl (by rw [hab'])))), mem_links.2 (Or.inl rfl),
        fun x hx => ?_⟩
      rw [mem_links] at hx
      rcases hx with h | h | h | h
      · exact Or.inr (congrArg Prod.snd h).symm
      · exact absurd (congrArg Prod.fst h) (by simp)
      · refine Or.inl (tshift_injective 1 ?_)
        rw [hab']
        exact (congrArg Prod.snd h).symm
      · exact absurd (congrArg Prod.fst h) (by simp)
  obtain ⟨i, h | h⟩ := h
  · exact key i h
  · obtain ⟨ℓ, h1, h2, h3⟩ := key i h
    exact ⟨ℓ, h2, h1, fun x hx => (h3 x hx).symm⟩

/-! ## 2. The peel along any free link -/

theorem face_update_a (hn : 2 ≤ n) (f : TSite 2 n) (W : TLink 2 n → SU N) (g : SU N) :
    face f (Function.update W (0, f) g)
      = 1 * g * (W (1, tshift 0 f) * (W (0, tshift 1 f))⁻¹ * (W (1, f))⁻¹) := by
  unfold face
  rw [Function.update_self, Function.update_of_ne pair_ne',
    Function.update_of_ne (pair_ne_of (tshift_ne hn 1 f)), Function.update_of_ne pair_ne']
  group

theorem face_update_d (hn : 2 ≤ n) (f : TSite 2 n) (W : TLink 2 n → SU N) (g : SU N) :
    face f (Function.update W (1, f) g)
      = (W (0, f) * W (1, tshift 0 f) * (W (0, tshift 1 f))⁻¹) * g⁻¹ * 1 := by
  unfold face
  rw [Function.update_of_ne pair_ne, Function.update_of_ne (pair_ne_of (tshift_ne hn 0 f)),
    Function.update_of_ne pair_ne, Function.update_self]
  group

/-- **A link of `f` integrates the face to its mean.** DERIVED: `2` the least side. -/
theorem free_mean (hn : 2 ≤ n) (s : SU N → ℝ) {f : TSite 2 n} {ℓ : TLink 2 n} (hℓ : ℓ ∈ links f)
    (W : TLink 2 n → SU N) :
    ∫ g, s (face f (Function.update W ℓ g)) ∂(probHaar (SU N)) = ∫ g, s g ∂(probHaar (SU N)) := by
  have hinv : ∀ A B : SU N, ∫ g, s (A * g⁻¹ * B) ∂(probHaar (SU N)) = ∫ g, s g ∂(probHaar (SU N)) :=
    fun A B => (integral_inv_eq_self (fun g => s (A * g * B)) (probHaar (SU N))).trans
      (HeatBath.integral_twoSided s A B)
  rcases mem_links.1 hℓ with rfl | rfl | rfl | rfl
  · simp_rw [face_update_a hn f W]
    exact HeatBath.integral_twoSided s _ _
  · simp_rw [face_update_e0 hn f W]
    exact HeatBath.integral_twoSided s _ _
  · simp_rw [face_update_e1 hn f W]
    exact hinv _ _
  · simp_rw [face_update_d hn f W]
    exact hinv _ _

/-- **`E` peels past `G`**, along any link. No numeral. -/
def Exits2 (E : Finset (TSite 2 n)) (G : (TLink 2 n → SU N) → ℝ) : Prop :=
  ∀ S, S ⊆ E → S.Nonempty → S ≠ E → ∃ f ∈ S, ∃ ℓ ∈ links f, NoRead G ℓ ∧ ∀ x ∈ S, x ≠ f → ℓ ∉ links x

theorem face_off {ℓ : TLink 2 n} {x : TSite 2 n} (h : ℓ ∉ links x) (W : TLink 2 n → SU N) (g : SU N) :
    face x (Function.update W ℓ g) = face x W := by
  rw [mem_links] at h
  push Not at h
  exact face_update_other W g h.1.symm h.2.1.symm h.2.2.1.symm h.2.2.2.symm

/-- **Peeling past `G`**: `∫ G ∏_S s = (∫ s)^{|S|} ∫ G` for `S ⊊ E`. DERIVED: `0`, `1` the range of `s`; `2` the least side. -/
theorem integral_mul_prod_peel2 (hn : 2 ≤ n) {s : SU N → ℝ} (hs : Continuous s) {G : (TLink 2 n → SU N) → ℝ}
    (hG : Continuous G) {E : Finset (TSite 2 n)} (hE : Exits2 E G) (k : ℕ) :
    ∀ S : Finset (TSite 2 n), S.card = k → S ⊆ E → S ≠ E →
      ∫ U, G U * ∏ x ∈ S, s (face x U) ∂(μL n N)
        = (∫ g, s g ∂(probHaar (SU N))) ^ k * ∫ U, G U ∂(μL n N) := by
  induction k with
  | zero =>
    intro S hS _ _
    rw [Finset.card_eq_zero.mp hS]
    simp
  | succ k ih =>
    intro S hS hSE hne
    have hnon : S.Nonempty := by rw [← Finset.card_pos, hS]; omega
    obtain ⟨f, hf, ℓ, hℓ, hread, hoff⟩ := hE S hSE hnon hne
    have hcard : (S.erase f).card = k := by rw [Finset.card_erase_of_mem hf, hS]; rfl
    have hsub : S.erase f ⊆ E := (Finset.erase_subset _ _).trans hSE
    have hne' : S.erase f ≠ E := fun h => Finset.notMem_erase f S (h ▸ hSE hf)
    have hIH := ih (S.erase f) hcard hsub hne'
    set c := ∫ g, s g ∂(probHaar (SU N)) with hc
    have hF : Continuous fun U : TLink 2 n → SU N => G U * ∏ x ∈ S, s (face x U) :=
      hG.mul (continuous_finsetProd _ fun x _ => hs.comp (continuous_face x))
    obtain ⟨C, hC⟩ := HeatBath.exists_abs_le hF
    rw [HeatBath.integral_eq_integral_update (probHaar (SU N)) ℓ _ hF.measurable hC]
    have hin : ∀ W : TLink 2 n → SU N,
        ∫ g, G (Function.update W ℓ g) * ∏ x ∈ S, s (face x (Function.update W ℓ g)) ∂(probHaar (SU N))
          = c * (G W * ∏ x ∈ S.erase f, s (face x W)) := by
      intro W
      have hsplit : ∀ g, G (Function.update W ℓ g) * ∏ x ∈ S, s (face x (Function.update W ℓ g))
          = s (face f (Function.update W ℓ g)) * (G W * ∏ x ∈ S.erase f, s (face x W)) := by
        intro g
        rw [hread W g, ← Finset.mul_prod_erase S _ hf,
          Finset.prod_congr rfl fun x hx => by
            rw [face_off (hoff x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)) W g]]
        ring
      simp_rw [hsplit]
      rw [integral_mul_const, free_mean hn s hℓ W]
    simp_rw [hin]
    rw [integral_const_mul, hIH, pow_succ]
    ring

/-- **The forgetting identity**, as `StripTail.forget_eq`. DERIVED: `2` the least side. -/
theorem forget_eq2 (hn : 2 ≤ n) (β : ℝ) {G : (TLink 2 n → SU N) → ℝ}
    (hG : Continuous G) {E : Finset (TSite 2 n)} (hE : Exits2 E G) :
    ∫ U, G U * ∏ x ∈ E, wt β (face x U) ∂(μL n N)
      = (bk N β ^ E.card - cm N β ^ E.card) * ∫ U, G U ∂(μL n N)
        + ∫ U, G U * ∏ x ∈ E, sw β (face x U) ∂(μL n N) := by
  have hexp : ∀ U : TLink 2 n → SU N, G U * ∏ x ∈ E, wt β (face x U)
      = ∑ t ∈ E.powerset, (G U * ∏ x ∈ t, sw β (face x U)) * ∏ _x ∈ E \ t, fl β := by
    intro U
    have e : ∏ x ∈ E, wt β (face x U) = ∏ x ∈ E, (sw β (face x U) + fl β) :=
      Finset.prod_congr rfl fun x _ => by unfold sw; ring
    rw [e, Finset.prod_add, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hint : ∀ t : Finset (TSite 2 n), Integrable
      (fun U => (G U * ∏ x ∈ t, sw β (face x U)) * ∏ _x ∈ E \ t, fl β) (μL n N) := fun t =>
    integrable_of_continuous ((hG.mul (continuous_finsetProd _ fun x _ =>
      (continuous_sw β).comp (continuous_face x))).mul continuous_const)
  simp_rw [hexp]
  rw [integral_finsetSum _ fun t _ => hint t]
  simp_rw [integral_mul_const, Finset.prod_const]
  have hconst : bk N β ^ E.card = ∑ t ∈ E.powerset, cm N β ^ t.card * fl β ^ (E \ t).card := by
    unfold bk
    rw [← Finset.prod_const, Finset.prod_add]
    simp only [Finset.prod_const]
  rw [hconst, ← Finset.add_sum_erase _ _ (Finset.mem_powerset_self E),
    ← Finset.add_sum_erase _ _ (Finset.mem_powerset_self E)]
  have hrest : ∀ t ∈ E.powerset.erase E,
      (∫ U, G U * ∏ x ∈ t, sw β (face x U) ∂(μL n N)) * fl β ^ (E \ t).card
        = cm N β ^ t.card * fl β ^ (E \ t).card * ∫ U, G U ∂(μL n N) := by
    intro t ht
    have hsub := Finset.mem_powerset.1 (Finset.mem_of_mem_erase ht)
    rw [integral_mul_prod_peel2 hn (continuous_sw β) hG hE t.card t rfl hsub (Finset.ne_of_mem_erase ht)]
    unfold cm
    ring
  rw [Finset.sum_congr rfl hrest, ← Finset.sum_mul, Finset.sdiff_self, Finset.card_empty, pow_zero,
    mul_one, mul_one]
  ring

/-- **The two-sided forgetting**, as `StripTail.forget_bounds`. DERIVED: `0` the sign of `G`; `2` the least side. -/
theorem forget_bounds2 (hN : N ≠ 0) (hn : 2 ≤ n) {β : ℝ} (hβ : 0 ≤ β) {G : (TLink 2 n → SU N) → ℝ}
    (hG : Continuous G) (hG0 : ∀ U, 0 ≤ G U) {E : Finset (TSite 2 n)} (hE : Exits2 E G) :
    (bk N β ^ E.card - cm N β ^ E.card) * ∫ U, G U ∂(μL n N)
        ≤ ∫ U, G U * ∏ x ∈ E, wt β (face x U) ∂(μL n N) ∧
      (1 - (1 - fl β) ^ E.card) * ∫ U, G U * ∏ x ∈ E, wt β (face x U) ∂(μL n N)
        ≤ (bk N β ^ E.card - cm N β ^ E.card) * ∫ U, G U ∂(μL n N) := by
  have he := forget_eq2 (N := N) hn β hG hE
  have hcw : Continuous fun U : TLink 2 n → SU N => G U * ∏ x ∈ E, wt β (face x U) :=
    hG.mul (continuous_finsetProd _ fun x _ => (continuous_wt β).comp (continuous_face x))
  have hcs : Continuous fun U : TLink 2 n → SU N => G U * ∏ x ∈ E, sw β (face x U) :=
    hG.mul (continuous_finsetProd _ fun x _ => (continuous_sw β).comp (continuous_face x))
  have hX0 : 0 ≤ ∫ U, G U * ∏ x ∈ E, sw β (face x U) ∂(μL n N) :=
    integral_nonneg fun U => mul_nonneg (hG0 U) (Finset.prod_nonneg fun x _ => sw_nonneg hN hβ _)
  have hX1 : ∫ U, G U * ∏ x ∈ E, sw β (face x U) ∂(μL n N)
      ≤ (1 - fl β) ^ E.card * ∫ U, G U * ∏ x ∈ E, wt β (face x U) ∂(μL n N) := by
    rw [← integral_const_mul]
    refine integral_mono (integrable_of_continuous hcs) ((integrable_of_continuous hcw).const_mul _)
      fun U => ?_
    have := mul_le_mul_of_nonneg_left (prod_sw_le hN hβ E U) (hG0 U)
    show G U * ∏ x ∈ E, sw β (face x U) ≤ (1 - fl β) ^ E.card * (G U * ∏ x ∈ E, wt β (face x U))
    linarith
  constructor <;> nlinarith

/-! ## 3. Connected sets of faces -/

/-- `S` is closed under adjacency inside `E`. No numeral. -/
def Closed (E S : Finset (TSite 2 n)) : Prop := ∀ f ∈ S, ∀ g ∈ E, Adj f g → g ∈ S

/-- `E` is connected: a nonempty closed subset is `E`. No numeral. -/
def Conn (E : Finset (TSite 2 n)) : Prop := ∀ S, S ⊆ E → S.Nonempty → Closed E S → S = E

theorem conn_univ (hn : 2 ≤ n) : Conn (Finset.univ : Finset (TSite 2 n)) := by
  intro S _ hne hcl
  by_contra hS
  obtain ⟨f, hf, h | h⟩ := exists_free hn hne hS
  · exact h (hcl f hf _ (Finset.mem_univ _) ⟨0, Or.inl rfl⟩)
  · exact h (hcl f hf _ (Finset.mem_univ _) ⟨1, Or.inl rfl⟩)

/-- **A connected exterior peels past `G`, if `G` reads no link outside `L`, and every link of `L` has a face outside `E`
on it.** No numeral. -/
theorem exits2_of_conn {E : Finset (TSite 2 n)} (hE : Conn E) {G : (TLink 2 n → SU N) → ℝ}
    (hG : ∀ f g, f ∈ E → g ∈ E → ∀ ℓ, ℓ ∈ links f → ℓ ∈ links g → (∀ x, ℓ ∈ links x → x = f ∨ x = g) → NoRead G ℓ) :
    Exits2 E G := by
  intro S hS hne hSE
  have hnc : ¬ Closed E S := fun hc => hSE (hE S hS hne hc)
  unfold Closed at hnc
  push Not at hnc
  obtain ⟨f, hf, g, hgE, hadj, hg⟩ := hnc
  obtain ⟨ℓ, h1, h2, h3⟩ := side_faces hadj
  refine ⟨f, hf, ℓ, h1, hG f g (hS hf) hgE ℓ h1 h2 h3, fun x hx hxf hc => ?_⟩
  rcases h3 x hc with h | h
  · exact hxf h
  · exact hg (h ▸ hx)

/-! ## 4. A rectangle and its ring -/

/-- **A rectangle of faces**, away from the seam of the coordinates. DERIVED: `0` the sign of the sides and the seam. -/
structure Rc (n : ℕ) where
  a : ℕ
  r : ℕ
  b : ℕ
  s : ℕ
  ha : 0 < a
  hb : 0 < b
  hr : a + r < n
  hs : b + s < n
  r0 : 0 < r
  s0 : 0 < s

/-- The faces of `R`, in coordinates. No numeral. -/
def InC (R : Rc n) (u v : ℕ) : Prop := R.a ≤ u ∧ u < R.a + R.r ∧ R.b ≤ v ∧ v < R.b + R.s

/-- `R` with its ring, in coordinates. DERIVED: `1` the width of the ring. -/
def ClC (R : Rc n) (u v : ℕ) : Prop := R.a ≤ u + 1 ∧ u ≤ R.a + R.r ∧ R.b ≤ v + 1 ∧ v ≤ R.b + R.s

theorem InC.cl {R : Rc n} {u v : ℕ} (h : InC R u v) : ClC R u v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- `x` is a face of `R`. No numeral. -/
def In (R : Rc n) (x : TSite 2 n) : Prop := InC R (x 0).val (x 1).val

/-- The separation of two rectangles: the first and its ring miss the second. No numeral. -/
def Sep (R R' : Rc n) : Prop := ∀ u v, ClC R u v → ¬ InC R' u v

theorem rot_val {a : Fin n} (h : a.val + 1 < n) : (finRotate n a).val = a.val + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [coe_finRotate]
  have : ¬ (a = Fin.last m) := fun e => by
    have := congrArg Fin.val e
    simp at this
    omega
  rw [if_neg this]

theorem rot_val_last {a : Fin n} (h : ¬ a.val + 1 < n) : (finRotate n a).val = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [coe_finRotate]
  have : a = Fin.last m := Fin.ext (by simp; omega)
  rw [if_pos this]

theorem tshift_zero_vals (x : TSite 2 n) : (tshift 0 x) 1 = x 1 ∧ (tshift 0 x) 0 = finRotate n (x 0) := by
  simp [tshift]

theorem tshift_one_vals (x : TSite 2 n) : (tshift 1 x) 0 = x 0 ∧ (tshift 1 x) 1 = finRotate n (x 1) := by
  simp [tshift]

/-- **A neighbour of `R` outside `R` is in the ring.** No numeral. -/
theorem adj_ring {R : Rc n} {f g : TSite 2 n} (hadj : Adj f g) (hg : In R g) :
    ClC R (f 0).val (f 1).val := by
  have ha := R.ha
  have hb := R.hb
  have hr := R.hr
  have hs := R.hs
  obtain ⟨h1, h2, h3, h4⟩ := hg
  obtain ⟨i, h | h⟩ := hadj
  · fin_cases i
    · have h0 : tshift 0 f = g := h
      obtain ⟨e1, e2⟩ := tshift_zero_vals f
      rw [h0] at e1 e2
      have e3 : (g 1).val = (f 1).val := by rw [e1]
      by_cases hw : (f 0).val + 1 < n
      · have e4 : (g 0).val = (f 0).val + 1 := by rw [e2]; exact rot_val hw
        exact ⟨by omega, by omega, by omega, by omega⟩
      · have e4 : (g 0).val = 0 := by rw [e2]; exact rot_val_last hw
        omega
    · have h0 : tshift 1 f = g := h
      obtain ⟨e1, e2⟩ := tshift_one_vals f
      rw [h0] at e1 e2
      have e3 : (g 0).val = (f 0).val := by rw [e1]
      by_cases hw : (f 1).val + 1 < n
      · have e4 : (g 1).val = (f 1).val + 1 := by rw [e2]; exact rot_val hw
        exact ⟨by omega, by omega, by omega, by omega⟩
      · have e4 : (g 1).val = 0 := by rw [e2]; exact rot_val_last hw
        omega
  · fin_cases i
    · have h0 : tshift 0 g = f := h
      obtain ⟨e1, e2⟩ := tshift_zero_vals g
      rw [h0] at e1 e2
      have e3 : (f 1).val = (g 1).val := by rw [e1]
      have hw : (g 0).val + 1 < n := by omega
      have e4 : (f 0).val = (g 0).val + 1 := by rw [e2]; exact rot_val hw
      exact ⟨by omega, by omega, by omega, by omega⟩
    · have h0 : tshift 1 g = f := h
      obtain ⟨e1, e2⟩ := tshift_one_vals g
      rw [h0] at e1 e2
      have e3 : (f 0).val = (g 0).val := by rw [e1]
      have hw : (g 1).val + 1 < n := by omega
      have e4 : (f 1).val = (g 1).val + 1 := by rw [e2]; exact rot_val hw
      exact ⟨by omega, by omega, by omega, by omega⟩

/-- The set `S` holds the face at `(u, v)`. No numeral. -/
def Mm (S : Finset (TSite 2 n)) (u v : ℕ) : Prop := ∀ x : TSite 2 n, (x 0).val = u → (x 1).val = v → x ∈ S

theorem exists_pt {u v : ℕ} (hu : u < n) (hv : v < n) : ∃ x : TSite 2 n, (x 0).val = u ∧ (x 1).val = v :=
  ⟨pt ⟨u, hu⟩ ⟨v, hv⟩, rfl, rfl⟩

theorem site_ext {x y : TSite 2 n} (h0 : (x 0).val = (y 0).val) (h1 : (x 1).val = (y 1).val) : x = y := by
  funext j
  fin_cases j
  · exact Fin.ext h0
  · exact Fin.ext h1

/-- One step along the first coordinate. No numeral. -/
theorem step0 {E S : Finset (TSite 2 n)} (hcl : Closed E S) {u v : ℕ} (hu : u + 1 < n) (hv : v < n)
    (hE : ∀ x : TSite 2 n, (x 0).val = u → (x 1).val = v → x ∈ E)
    (hE' : ∀ x : TSite 2 n, (x 0).val = u + 1 → (x 1).val = v → x ∈ E) : Mm S u v ↔ Mm S (u + 1) v := by
  constructor
  · intro h y hy0 hy1
    obtain ⟨x, h0, h1⟩ := exists_pt (n := n) (show u < n by omega) hv
    have hxy : tshift 0 x = y := by
      obtain ⟨e1, e2⟩ := tshift_zero_vals x
      refine site_ext ?_ ?_
      · rw [e2, rot_val (by omega), h0, hy0]
      · rw [e1, h1, hy1]
    exact hcl x (h x h0 h1) y (hE' y hy0 hy1) ⟨0, Or.inl hxy⟩
  · intro h y hy0 hy1
    obtain ⟨e1, e2⟩ := tshift_zero_vals y
    have h3 : (tshift 0 y 0).val = u + 1 := by rw [e2, rot_val (by omega), hy0]
    have h4 : (tshift 0 y 1).val = v := by rw [e1, hy1]
    exact hcl _ (h _ h3 h4) y (hE y hy0 hy1) ⟨0, Or.inr rfl⟩

/-- One step along the second coordinate. No numeral. -/
theorem step1 {E S : Finset (TSite 2 n)} (hcl : Closed E S) {u v : ℕ} (hu : u < n) (hv : v + 1 < n)
    (hE : ∀ x : TSite 2 n, (x 0).val = u → (x 1).val = v → x ∈ E)
    (hE' : ∀ x : TSite 2 n, (x 0).val = u → (x 1).val = v + 1 → x ∈ E) : Mm S u v ↔ Mm S u (v + 1) := by
  constructor
  · intro h y hy0 hy1
    obtain ⟨x, h0, h1⟩ := exists_pt (n := n) hu (show v < n by omega)
    have hxy : tshift 1 x = y := by
      obtain ⟨e1, e2⟩ := tshift_one_vals x
      refine site_ext ?_ ?_
      · rw [e1, h0, hy0]
      · rw [e2, rot_val (by omega), h1, hy1]
    exact hcl x (h x h0 h1) y (hE' y hy0 hy1) ⟨1, Or.inl hxy⟩
  · intro h y hy0 hy1
    obtain ⟨e1, e2⟩ := tshift_one_vals y
    have h3 : (tshift 1 y 0).val = u := by rw [e1, hy0]
    have h4 : (tshift 1 y 1).val = v + 1 := by rw [e2, rot_val (by omega), hy1]
    exact hcl _ (h _ h3 h4) y (hE y hy0 hy1) ⟨1, Or.inr rfl⟩

/-- A walk along a row of `E`. DERIVED: `1` the step. -/
theorem walk0 {E S : Finset (TSite 2 n)} (hcl : Closed E S) {u v : ℕ} (hv : v < n) (k : ℕ)
    (hk : u + k < n) (hE : ∀ c ≤ k, ∀ x : TSite 2 n, (x 0).val = u + c → (x 1).val = v → x ∈ E) :
    Mm S u v ↔ Mm S (u + k) v := by
  induction k with
  | zero => exact Iff.rfl
  | succ k ih =>
    exact (ih (by omega) fun c hc => hE c (by omega)).trans
      (step0 hcl (by omega) hv (hE k (by omega)) (hE (k + 1) le_rfl))

/-- A walk along a column of `E`. DERIVED: `1` the step. -/
theorem walk1 {E S : Finset (TSite 2 n)} (hcl : Closed E S) {u v : ℕ} (hu : u < n) (k : ℕ)
    (hk : v + k < n) (hE : ∀ c ≤ k, ∀ x : TSite 2 n, (x 0).val = u → (x 1).val = v + c → x ∈ E) :
    Mm S u v ↔ Mm S u (v + k) := by
  induction k with
  | zero => exact Iff.rfl
  | succ k ih =>
    exact (ih (by omega) fun c hc => hE c (by omega)).trans
      (step1 hcl hu (by omega) (hE k (by omega)) (hE (k + 1) le_rfl))

/-- **The ring is connected**: a set closed in `E ⊇ ring` holds every point of the ring or none. Every point is walked to the
lower left corner. DERIVED: `1` the width of the ring. -/
theorem ring_all {R : Rc n} {E S : Finset (TSite 2 n)} (hcl : Closed E S)
    (hE : ∀ x : TSite 2 n, ClC R (x 0).val (x 1).val → ¬ InC R (x 0).val (x 1).val → x ∈ E)
    {u v : ℕ} (hC : ClC R u v) (hI : ¬ InC R u v) :
    Mm S (R.a - 1) (R.b - 1) ↔ Mm S u v := by
  have ha := R.ha
  have hb := R.hb
  have hr := R.hr
  have hs := R.hs
  have hr0 := R.r0
  have hs0 := R.s0
  obtain ⟨c1, c2, c3, c4⟩ := hC
  have hEx : ∀ (p q : ℕ), ClC R p q → ¬ InC R p q → ∀ x : TSite 2 n, (x 0).val = p → (x 1).val = q → x ∈ E := by
    intro p q h1 h2 x h3 h4
    exact hE x (by rw [h3, h4]; exact h1) (by rw [h3, h4]; exact h2)
  have bot : ∀ k, R.a - 1 + k ≤ R.a + R.r → (Mm S (R.a - 1) (R.b - 1) ↔ Mm S (R.a - 1 + k) (R.b - 1)) := by
    intro k hk
    refine walk0 hcl (by omega) k (by omega) fun c hc => hEx _ _ ⟨by omega, by omega, by omega, by omega⟩ ?_
    rintro ⟨-, -, h, -⟩
    omega
  have left : ∀ k, R.b - 1 + k ≤ R.b + R.s → (Mm S (R.a - 1) (R.b - 1) ↔ Mm S (R.a - 1) (R.b - 1 + k)) := by
    intro k hk
    refine walk1 hcl (by omega) k (by omega) fun c hc => hEx _ _ ⟨by omega, by omega, by omega, by omega⟩ ?_
    rintro ⟨h, -, -, -⟩
    omega
  have top : ∀ k, R.a - 1 + k ≤ R.a + R.r →
      (Mm S (R.a - 1) (R.b + R.s) ↔ Mm S (R.a - 1 + k) (R.b + R.s)) := by
    intro k hk
    refine walk0 hcl (by omega) k (by omega) fun c hc => hEx _ _ ⟨by omega, by omega, by omega, by omega⟩ ?_
    rintro ⟨-, -, -, h⟩
    omega
  have right : ∀ k, R.b - 1 + k ≤ R.b + R.s →
      (Mm S (R.a + R.r) (R.b - 1) ↔ Mm S (R.a + R.r) (R.b - 1 + k)) := by
    intro k hk
    refine walk1 hcl (by omega) k (by omega) fun c hc => hEx _ _ ⟨by omega, by omega, by omega, by omega⟩ ?_
    rintro ⟨-, h, -, -⟩
    omega
  have hTL := left (R.s + 1) (by omega)
  have hBR := bot (R.r + 1) (by omega)
  rw [show R.b - 1 + (R.s + 1) = R.b + R.s by omega] at hTL
  rw [show R.a - 1 + (R.r + 1) = R.a + R.r by omega] at hBR
  have hside : u = R.a - 1 ∨ u = R.a + R.r ∨ v = R.b - 1 ∨ v = R.b + R.s := by
    by_contra hc
    push Not at hc
    exact hI ⟨by omega, by omega, by omega, by omega⟩
  rcases hside with rfl | rfl | rfl | rfl
  · have := left (v - (R.b - 1)) (by omega)
    rwa [show R.b - 1 + (v - (R.b - 1)) = v by omega] at this
  · have := right (v - (R.b - 1)) (by omega)
    rw [show R.b - 1 + (v - (R.b - 1)) = v by omega] at this
    exact hBR.trans this
  · have := bot (u - (R.a - 1)) (by omega)
    rwa [show R.a - 1 + (u - (R.a - 1)) = u by omega] at this
  · have := top (u - (R.a - 1)) (by omega)
    rw [show R.a - 1 + (u - (R.a - 1)) = u by omega] at this
    exact hTL.trans this

/-! ## 5. The exterior of separated rectangles is connected -/

variable {ι : Type} [DecidableEq ι]

open scoped Classical in
/-- **The exterior** of the rectangles of `T`. No numeral. -/
def outT (R : ι → Rc n) (T : Finset ι) : Finset (TSite 2 n) :=
  Finset.univ.filter fun x => ∀ i ∈ T, ¬ In (R i) x

theorem mem_outT {R : ι → Rc n} {T : Finset ι} {x : TSite 2 n} : x ∈ outT R T ↔ ∀ i ∈ T, ¬ In (R i) x := by
  classical
  simp [outT]

/-- **Putting a rectangle back**: the exterior stays connected. Case on whether a closed set meets the ring. No numeral. -/
theorem conn_insert {R : ι → Rc n} (hsep : ∀ i j, i ≠ j → Sep (R i) (R j)) {T : Finset ι} {j : ι} (hj : j ∉ T)
    (hC : Conn (outT R T)) : Conn (outT R (insert j T)) := by
  classical
  set E := outT R T with hE
  set E' := outT R (insert j T) with hE'
  have hne : ∀ i ∈ T, i ≠ j := fun i hi e => hj (e ▸ hi)
  have hring : ∀ x : TSite 2 n, ClC (R j) (x 0).val (x 1).val → ¬ InC (R j) (x 0).val (x 1).val → x ∈ E' := by
    intro x h1 h2
    refine mem_outT.2 fun i hi => ?_
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact h2
    · exact hsep j i (hne i hi).symm _ _ h1
  have hsub : E' ⊆ E := fun x hx => mem_outT.2 fun i hi => mem_outT.1 hx i (Finset.mem_insert_of_mem hi)
  have hRin : ∀ x, In (R j) x → x ∈ E := fun x hx =>
    mem_outT.2 fun i hi => hsep j i (hne i hi).symm _ _ hx.cl
  have hmem : ∀ x, x ∈ E → ¬ In (R j) x → x ∈ E' := by
    intro x hx hn
    refine mem_outT.2 fun i hi => ?_
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hn
    · exact mem_outT.1 hx i hi
  intro S hS hnon hcl
  have hSn : ∀ x ∈ S, ¬ In (R j) x := fun x hx => mem_outT.1 (hS hx) j (Finset.mem_insert_self _ _)
  by_cases hmeet : Mm S ((R j).a - 1) ((R j).b - 1)
  · -- the ring lies in `S`: fill `R j` in
    have hringS : ∀ x : TSite 2 n, ClC (R j) (x 0).val (x 1).val → ¬ In (R j) x → x ∈ S := fun x h1 h2 =>
      ((ring_all hcl hring h1 h2).1 hmeet) x rfl rfl
    have hall := hC (S ∪ Finset.univ.filter fun x => In (R j) x) (by
        intro x hx
        rcases Finset.mem_union.1 hx with h | h
        · exact hsub (hS h)
        · exact hRin x (Finset.mem_filter.1 h).2)
      (hnon.mono Finset.subset_union_left) (by
        intro f hf g hg hadj
        by_cases hgR : In (R j) g
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hgR⟩)
        · refine Finset.mem_union_left _ ?_
          rcases Finset.mem_union.1 hf with h | h
          · exact hcl f h g (hmem g hg hgR) hadj
          · exact hringS g (adj_ring (adj_symm hadj) (Finset.mem_filter.1 h).2) hgR)
    refine Finset.Subset.antisymm hS fun x hx => ?_
    have hxE := hsub hx
    rw [← hall] at hxE
    rcases Finset.mem_union.1 hxE with h | h
    · exact h
    · exact absurd (Finset.mem_filter.1 h).2 (mem_outT.1 hx j (Finset.mem_insert_self _ _))
  · -- the ring misses `S`: `S` is closed in the larger exterior, which contains `R j`
    have hno : ∀ x ∈ S, ¬ ClC (R j) (x 0).val (x 1).val := by
      intro x hx hc
      refine hmeet ?_
      have h2 : ¬ InC (R j) (x 0).val (x 1).val := hSn x hx
      refine (ring_all hcl hring hc h2).2 ?_
      intro y h3 h4
      have : y = x := site_ext h3 h4
      rw [this]
      exact hx
    have hall := hC S (hS.trans hsub) hnon (by
      intro f hf g hg hadj
      have hgR : ¬ In (R j) g := fun h => hno f hf (adj_ring hadj h)
      exact hcl f hf g (hmem g hg hgR) hadj)
    have ha := (R j).ha
    have hb := (R j).hb
    have hr := (R j).hr
    have hs := (R j).hs
    have hr0 := (R j).r0
    have hs0 := (R j).s0
    obtain ⟨y, h0, h1⟩ := exists_pt (n := n) (show (R j).a < n by omega) (show (R j).b < n by omega)
    have hyR : In (R j) y := by
      show InC (R j) (y 0).val (y 1).val
      rw [h0, h1]
      exact ⟨le_rfl, by omega, le_rfl, by omega⟩
    have := hRin y hyR
    rw [← hall] at this
    exact absurd hyR (hSn y this)

/-- **The exterior of separated rectangles is connected.** DERIVED: `2` the least side. -/
theorem conn_outT (hn : 2 ≤ n) {R : ι → Rc n} (hsep : ∀ i j, i ≠ j → Sep (R i) (R j)) (T : Finset ι) :
    Conn (outT R T) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have e : outT R ∅ = Finset.univ := by
      ext x
      simp [mem_outT]
    rw [e]
    exact conn_univ hn
  | insert j T hj ih => exact conn_insert hsep hj ih

/-! ## 6. Factorization over disjoint link sets -/

/-- `G` reads the links of `L` only. No numeral. -/
def ReadsOn (L : Finset (TLink 2 n)) (G : (TLink 2 n → SU N) → ℝ) : Prop :=
  ∀ W W' : TLink 2 n → SU N, (∀ ℓ ∈ L, W ℓ = W' ℓ) → G W = G W'

theorem int_mul {L L' : Finset (TLink 2 n)} (hd : Disjoint L L') {F F' : (TLink 2 n → SU N) → ℝ}
    (hF : Continuous F) (hF' : Continuous F') (hr : ReadsOn L F) (hr' : ReadsOn L' F') :
    ∫ U, F U * F' U ∂(μL n N) = (∫ U, F U ∂(μL n N)) * ∫ U, F' U ∂(μL n N) := by
  have key := WilsonReal.block_integral_factor (N := N) L L' hd
    (fun v => F (StripGas.ext1 _ v)) (fun v => F' (StripGas.ext1 _ v))
    (hF.comp (StripGas.continuous_ext1 _)).measurable (hF'.comp (StripGas.continuous_ext1 _)).measurable
  have e : ∀ (M : Finset (TLink 2 n)) (H : (TLink 2 n → SU N) → ℝ), ReadsOn M H → ∀ a : TLink 2 n → SU N,
      H (StripGas.ext1 M fun i => a i.val) = H a := by
    intro M H hH a
    refine hH _ _ fun z hz => ?_
    simp only [StripGas.ext1, dif_pos hz]
  simp only [e L F hr, e L' F' hr'] at key
  exact key

/-- The links of the faces of `R`. No numeral. -/
def rl (R : Rc n) : Finset (TLink 2 n) := by
  classical
  exact (Finset.univ.filter fun x => In R x).biUnion links

/-- The faces of `R`. No numeral. -/
def fcs (R : Rc n) : Finset (TSite 2 n) := by
  classical
  exact Finset.univ.filter fun x => In R x

theorem mem_fcs {R : Rc n} {x : TSite 2 n} : x ∈ fcs R ↔ In R x := by
  classical
  simp [fcs]

theorem mem_rl {R : Rc n} {ℓ : TLink 2 n} : ℓ ∈ rl R ↔ ∃ x, In R x ∧ ℓ ∈ links x := by
  classical
  simp [rl]

/-- **Separated rectangles have disjoint links.** No numeral. -/
theorem rl_disjoint {R R' : Rc n} (h : Sep R R') (h' : Sep R' R) : Disjoint (rl R) (rl R') := by
  rw [Finset.disjoint_left]
  intro ℓ h1 h2
  obtain ⟨x, hx, hl⟩ := mem_rl.1 h1
  obtain ⟨y, hy, hl'⟩ := mem_rl.1 h2
  rcases link_shared hl hl' with rfl | hadj
  · exact h _ _ hx.cl hy
  · exact h' _ _ (adj_ring hadj hy) hx

/-- **The integral of a product over separated rectangles factors.** No numeral. -/
theorem int_prod {R : ι → Rc n} (hsep : ∀ i j, i ≠ j → Sep (R i) (R j)) {H : ι → (TLink 2 n → SU N) → ℝ}
    (hc : ∀ i, Continuous (H i)) (hr : ∀ i, ReadsOn (rl (R i)) (H i)) (T : Finset ι) :
    ∫ U, ∏ i ∈ T, H i U ∂(μL n N) = ∏ i ∈ T, ∫ U, H i U ∂(μL n N) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert j T hj ih =>
    simp only [Finset.prod_insert hj]
    rw [← ih]
    refine int_mul (L := rl (R j)) (L' := T.biUnion fun i => rl (R i)) ?_ (hc j)
      (continuous_finsetProd _ fun i _ => hc i) (hr j) ?_
    · rw [Finset.disjoint_biUnion_right]
      intro i hi
      have hne : j ≠ i := fun e => hj (e ▸ hi)
      exact rl_disjoint (hsep j i hne) (hsep i j hne.symm)
    · intro W W' hag
      refine Finset.prod_congr rfl fun i hi => hr i W W' fun ℓ hℓ => hag ℓ ?_
      exact Finset.mem_biUnion.2 ⟨i, hi, hℓ⟩

/-! ## 7. The forgetting for many rectangles -/

/-- The weight of a rectangle. No numeral. -/
def wR (β : ℝ) (R : Rc n) (U : TLink 2 n → SU N) : ℝ := ∏ x ∈ fcs R, wt β (face x U)

theorem continuous_wR (β : ℝ) (R : Rc n) : Continuous (wR (N := N) β R) :=
  continuous_finsetProd _ fun x _ => (continuous_wt β).comp (continuous_face x)

theorem wR_reads (β : ℝ) (R : Rc n) : ReadsOn (rl R) (wR (N := N) β R) := by
  intro W W' hag
  unfold wR
  refine Finset.prod_congr rfl fun x hx => ?_
  have hxR := mem_fcs.1 hx
  have e : face x W = face x W' := by
    unfold face
    have h : ∀ ℓ ∈ links x, W ℓ = W' ℓ := fun ℓ hℓ => hag ℓ (mem_rl.2 ⟨x, hxR, hℓ⟩)
    rw [h (0, x) (mem_links.2 (Or.inl rfl)), h (1, tshift 0 x) (mem_links.2 (Or.inr (Or.inl rfl))),
      h (0, tshift 1 x) (mem_links.2 (Or.inr (Or.inr (Or.inl rfl)))),
      h (1, x) (mem_links.2 (Or.inr (Or.inr (Or.inr rfl))))]
  rw [e]

/-- **The torus weight splits at the rectangles.** No numeral. -/
theorem prod_split_T {R : ι → Rc n} (hsep : ∀ i j, i ≠ j → Sep (R i) (R j)) (T : Finset ι) (β : ℝ)
    (U : TLink 2 n → SU N) :
    ∏ x, wt β (face x U) = (∏ i ∈ T, wR β (R i) U) * ∏ x ∈ outT R T, wt β (face x U) := by
  classical
  have hd : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (fcs (R i)) (fcs (R j)) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact hsep i j hij _ _ (mem_fcs.1 h1).cl (mem_fcs.1 h2)
  have h1 : ∏ i ∈ T, wR β (R i) U = ∏ x ∈ T.biUnion fun i => fcs (R i), wt β (face x U) := by
    rw [Finset.prod_biUnion hd]
    rfl
  have h2 : outT R T = (T.biUnion fun i => fcs (R i))ᶜ := by
    ext x
    rw [mem_outT, Finset.mem_compl, Finset.mem_biUnion]
    constructor
    · rintro h ⟨i, hi, hx⟩
      exact h i hi (mem_fcs.1 hx)
    · intro h i hi hx
      exact h ⟨i, hi, mem_fcs.2 hx⟩
  rw [h1, h2, Finset.prod_mul_prod_compl]

/-- **Functions of separated rectangles under the torus measure**: for `G_i ≥ 0` continuous reading the links of `R i`, with
`e` the exterior area, `m = b^e − c^e`, `δ = (1 − fl)^e`, `H_i = G_i W_i`:
`m ∏_i ∫ H_i ≤ ∫ ∏_i G_i ∏_x wt`, `(1 − δ) ∫ ∏_i G_i ∏_x wt ≤ m ∏_i ∫ H_i`. DERIVED: `2` the least side. -/
theorem multi_forget (hN : N ≠ 0) (hn : 2 ≤ n) {β : ℝ} (hβ : 0 ≤ β) {R : ι → Rc n}
    (hsep : ∀ i j, i ≠ j → Sep (R i) (R j)) (T : Finset ι) {G : ι → (TLink 2 n → SU N) → ℝ}
    (hc : ∀ i, Continuous (G i)) (hG0 : ∀ i U, 0 ≤ G i U) (hr : ∀ i, ReadsOn (rl (R i)) (G i)) :
    (bk N β ^ (outT R T).card - cm N β ^ (outT R T).card) * ∏ i ∈ T, ∫ U, G i U * wR β (R i) U ∂(μL n N)
        ≤ ∫ U, (∏ i ∈ T, G i U) * ∏ x, wt β (face x U) ∂(μL n N) ∧
      (1 - (1 - fl β) ^ (outT R T).card) * ∫ U, (∏ i ∈ T, G i U) * ∏ x, wt β (face x U) ∂(μL n N)
        ≤ (bk N β ^ (outT R T).card - cm N β ^ (outT R T).card)
          * ∏ i ∈ T, ∫ U, G i U * wR β (R i) U ∂(μL n N) := by
  classical
  obtain ⟨H, hH⟩ : ∃ H : ι → (TLink 2 n → SU N) → ℝ, H = fun i U => G i U * wR β (R i) U := ⟨_, rfl⟩
  have hHv : ∀ i U, H i U = G i U * wR β (R i) U := fun i U => by rw [hH]
  have hHc : ∀ i, Continuous (H i) := fun i => by
    rw [hH]
    exact (hc i).mul (continuous_wR β (R i))
  have hHr : ∀ i, ReadsOn (rl (R i)) (H i) := fun i W W' hag => by
    rw [hHv, hHv, hr i W W' hag, wR_reads β (R i) W W' hag]
  have hPc : Continuous fun U : TLink 2 n → SU N => ∏ i ∈ T, H i U :=
    continuous_finsetProd _ fun i _ => hHc i
  have hP0 : ∀ U : TLink 2 n → SU N, 0 ≤ ∏ i ∈ T, H i U := fun U =>
    Finset.prod_nonneg fun i _ => by
      rw [hHv]
      exact mul_nonneg (hG0 i U) (Finset.prod_nonneg fun _ _ => wt_nonneg _ _)
  have hex : Exits2 (outT R T) (fun U : TLink 2 n → SU N => ∏ i ∈ T, H i U) := by
    refine exits2_of_conn (conn_outT hn hsep T) fun f g hf hg ℓ _ _ h3 W b => ?_
    refine Finset.prod_congr rfl fun i hi => hHr i _ _ fun l hl => ?_
    refine Function.update_of_ne (fun e => ?_) _ _
    subst e
    obtain ⟨x, hxR, hxl⟩ := mem_rl.1 hl
    rcases h3 x hxl with rfl | rfl
    · exact mem_outT.1 hf i hi hxR
    · exact mem_outT.1 hg i hi hxR
  have hb := forget_bounds2 hN hn hβ hPc hP0 hex
  have e : ∫ U, (∏ i ∈ T, H i U) * ∏ x ∈ outT R T, wt β (face x U) ∂(μL n N)
      = ∫ U, (∏ i ∈ T, G i U) * ∏ x, wt β (face x U) ∂(μL n N) := by
    refine integral_congr_ae (Eventually.of_forall fun U => ?_)
    show (∏ i ∈ T, H i U) * _ = (∏ i ∈ T, G i U) * ∏ x, wt β (face x U)
    rw [prod_split_T hsep T β U]
    simp only [hHv, Finset.prod_mul_distrib]
    ring
  have e2 : ∫ U, ∏ i ∈ T, H i U ∂(μL n N) = ∏ i ∈ T, ∫ U, G i U * wR β (R i) U ∂(μL n N) := by
    rw [int_prod hsep hHc hHr T]
    exact Finset.prod_congr rfl fun i _ => integral_congr_ae (Eventually.of_forall fun U => hHv i U)
  rw [e, e2] at hb
  exact hb

/-- The mean of `G` on the free rectangle. No numeral. -/
def boxM (β : ℝ) (R : Rc n) (G : (TLink 2 n → SU N) → ℝ) : ℝ :=
  (∫ U, G U * wR β R U ∂(μL n N)) / ∫ U, wR β R U ∂(μL n N)

/-- The Wilson torus mean. No numeral. -/
def torM (β : ℝ) (G : (TLink 2 n → SU N) → ℝ) : ℝ :=
  (∫ U, G U * ∏ x, wt β (face x U) ∂(μL n N)) / ∫ U, ∏ x, wt β (face x U) ∂(μL n N)

theorem wR_int_pos (hN : N ≠ 0) (R : Rc n) (β : ℝ) : 0 < ∫ U, wR (N := N) β R U ∂(μL n N) := by
  have hc := continuous_wR (N := N) β R
  have hl : 0 < (∏ _x ∈ fcs R, Real.exp (-(4 * |β|)) : ℝ) := Finset.prod_pos fun _ _ => Real.exp_pos _
  refine lt_of_lt_of_le hl ?_
  have h0 : ∫ _U, (∏ _x ∈ fcs R, Real.exp (-(4 * |β|)) : ℝ) ∂(μL n N)
      = ∏ _x ∈ fcs R, Real.exp (-(4 * |β|)) := by simp
  rw [← h0]
  refine integral_mono (integrable_const _) (integrable_of_continuous hc) fun U => ?_
  refine Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun x _ => ?_
  unfold wt
  rw [Real.exp_le_exp]
  have h1 := WilsonAction.wilsonDensity_le_two hN (face x U)
  have h2 := WilsonAction.wilsonDensity_le_two hN (face x U)⁻¹
  have h3 := WilsonAction.wilsonDensity_nonneg hN (face x U)
  have h4 := WilsonAction.wilsonDensity_nonneg hN (face x U)⁻¹
  have h5 := neg_abs_le β
  have h6 := le_abs_self β
  have h7 := abs_nonneg β
  nlinarith

/-- **Separated rectangles are independent, up to the exterior**: for `e ≠ 0`,
`(1 − δ) ∏_i μ_i(G_i) ≤ ⟨∏_i G_i⟩ ≤ ∏_i μ_i(G_i)/(1 − δ)`, with `δ = (1 − e^{−4β})^e`. The error is relative to the value.
DERIVED: `2` the least side; `1` the unit of the ratio. -/
theorem multi_mean (hN : N ≠ 0) (hn : 2 ≤ n) {β : ℝ} (hβ : 0 ≤ β) {R : ι → Rc n}
    (hsep : ∀ i j, i ≠ j → Sep (R i) (R j)) (T : Finset ι) (he : (outT R T).card ≠ 0)
    {G : ι → (TLink 2 n → SU N) → ℝ} (hc : ∀ i, Continuous (G i)) (hG0 : ∀ i U, 0 ≤ G i U)
    (hr : ∀ i, ReadsOn (rl (R i)) (G i)) :
    (1 - (1 - fl β) ^ (outT R T).card) * ∏ i ∈ T, boxM β (R i) (G i)
        ≤ torM β (fun U => ∏ i ∈ T, G i U) ∧
      torM β (fun U => ∏ i ∈ T, G i U) ≤ (∏ i ∈ T, boxM β (R i) (G i)) / (1 - (1 - fl β) ^ (outT R T).card) := by
  classical
  obtain ⟨h1, h2⟩ := multi_forget hN hn hβ hsep T hc hG0 hr
  obtain ⟨h3, h4⟩ := multi_forget hN hn hβ hsep T (G := fun _ _ => (1 : ℝ)) (fun _ => continuous_const)
    (fun _ _ => zero_le_one) (fun _ _ _ _ => rfl)
  simp only [Finset.prod_const_one, one_mul] at h3 h4
  obtain ⟨e', he'⟩ : ∃ e', e' = (outT R T).card := ⟨_, rfl⟩
  rw [← he'] at h1 h2 h3 h4 ⊢
  have he0 : e' ≠ 0 := he' ▸ he
  have hδ1 : (1 - fl β) ^ e' < 1 :=
    pow_lt_one₀ (by linarith [fl_le_one hβ]) (by linarith [fl_pos β]) he0
  have hd0 : 0 < 1 - (1 - fl β) ^ e' := by linarith
  have hm : 0 < bk N β ^ e' - cm N β ^ e' := by
    have hlt : cm N β ^ e' < bk N β ^ e' := by
      unfold bk
      exact pow_lt_pow_left₀ (by linarith [fl_pos β]) (cm_nonneg hN hβ) he0
    linarith
  obtain ⟨m, hmd⟩ : ∃ m, m = bk N β ^ e' - cm N β ^ e' := ⟨_, rfl⟩
  obtain ⟨d, hdd⟩ : ∃ d, d = 1 - (1 - fl β) ^ e' := ⟨_, rfl⟩
  rw [← hmd] at h1 h2 h3 h4 hm
  rw [← hdd] at h2 h4 hd0 ⊢
  obtain ⟨A, hA⟩ : ∃ A, A = ∫ U, (∏ i ∈ T, G i U) * ∏ x, wt β (face x U) ∂(μL n N) := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ∫ U, ∏ x, wt β (face x U) ∂(μL n N) := ⟨_, rfl⟩
  have hBpos : ∀ i, 0 < ∫ U, wR (N := N) β (R i) U ∂(μL n N) := fun i => wR_int_pos hN _ _
  have hB1pos : 0 < ∏ i ∈ T, ∫ U, wR (N := N) β (R i) U ∂(μL n N) := Finset.prod_pos fun i _ => hBpos i
  obtain ⟨B, hB⟩ : ∃ B, B = ∏ i ∈ T, ∫ U, G i U * wR β (R i) U ∂(μL n N) := ⟨_, rfl⟩
  obtain ⟨B1, hB1d⟩ : ∃ B1, B1 = ∏ i ∈ T, ∫ U, wR (N := N) β (R i) U ∂(μL n N) := ⟨_, rfl⟩
  have hB1 : 0 < B1 := hB1d ▸ hB1pos
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact Finset.prod_nonneg fun i _ => integral_nonneg fun U => mul_nonneg (hG0 i U)
      (Finset.prod_nonneg fun _ _ => wt_nonneg _ _)
  have h3' : m * B1 ≤ Z := by
    rw [hB1d, hZ]
    simpa using h3
  have h4' : d * Z ≤ m * B1 := by
    rw [hB1d, hZ]
    simpa using h4
  rw [← hB, ← hA] at h1 h2
  have hZpos : 0 < Z := lt_of_lt_of_le (mul_pos hm hB1) h3'
  have ebox : ∏ i ∈ T, boxM β (R i) (G i) = B / B1 := by
    unfold boxM
    rw [Finset.prod_div_distrib, hB, hB1d]
  have etor : torM β (fun U => ∏ i ∈ T, G i U) = A / Z := by
    unfold torM
    rw [hA, hZ]
  rw [ebox, etor]
  constructor
  · rw [mul_div_assoc', div_le_div_iff₀ hB1 hZpos]
    have hk : d * Z * (m * B) ≤ m * B1 * A := mul_le_mul h4' h1 (by positivity) (by positivity)
    have : m * (d * B * Z) ≤ m * (A * B1) := by
      calc m * (d * B * Z) = d * Z * (m * B) := by ring
        _ ≤ m * B1 * A := hk
        _ = m * (A * B1) := by ring
    exact le_of_mul_le_mul_left this hm
  · rw [div_div, div_le_div_iff₀ hZpos (by positivity)]
    have hk : d * A * (m * B1) ≤ m * B * Z := mul_le_mul h2 h3' (by positivity) (by positivity)
    have : m * (A * (B1 * d)) ≤ m * (B * Z) := by
      calc m * (A * (B1 * d)) = d * A * (m * B1) := by ring
        _ ≤ m * B * Z := hk
        _ = m * (B * Z) := by ring
    exact le_of_mul_le_mul_left this hm

end MassGap.StripNest

#print axioms MassGap.StripNest.link_shared
#print axioms MassGap.StripNest.side_faces
#print axioms MassGap.StripNest.free_mean
#print axioms MassGap.StripNest.integral_mul_prod_peel2
#print axioms MassGap.StripNest.forget_eq2
#print axioms MassGap.StripNest.forget_bounds2
#print axioms MassGap.StripNest.exits2_of_conn
#print axioms MassGap.StripNest.ring_all
#print axioms MassGap.StripNest.conn_insert
#print axioms MassGap.StripNest.conn_outT
#print axioms MassGap.StripNest.rl_disjoint
#print axioms MassGap.StripNest.int_prod
#print axioms MassGap.StripNest.prod_split_T
#print axioms MassGap.StripNest.multi_forget
#print axioms MassGap.StripNest.multi_mean
#print axioms MassGap.StripNest.wR_int_pos
#print axioms MassGap.StripNest.continuous_wR
#print axioms MassGap.StripNest.wR_reads
