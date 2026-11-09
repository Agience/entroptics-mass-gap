import Mathlib
import MassGap.AxisSplit

/-!
# MassGap.TransverseTunnel — a line-spectral, positive corner function for which (T) fails

`AxisSplit.TransverseDouble x` (inequality (T): `x(v+e_μ+e_ν) + 4x(v) ≥ 2x(v+e_μ) + 2x(v+e_ν)` for `μ ≠ ν`, the
same as `0 ≤ mixed`) is one of the two open inputs of `AxisSplit.window_le`. This module shows that it is not a
consequence of the spectral structure the tree proves for the Wilson corner function: it builds a corner function that
is `CasimirStep.LineSpectral` (every dyadic line, in every direction, from every corner, is `log` of the traces of one
finite nonnegative spectrum) and `DoublingRecursion.Positive`, and for which (T) fails. Declarations are in the
namespace `MassGap.TransverseTunnel`.

## The model

`tunX K u = log Z`, `Z = (e^κ + e^{−κ})^N + (e^κ − e^{−κ})^N`, `κ = K · 2^{u_0+u_2+u_3}`, `N = 2^{u_1}`. It is the Ising
ring of `N` spins along axis `1` with coupling `κ`: the periodic `2 × 2` transfer `[[e^κ, e^{−κ}], [e^{−κ}, e^κ]]` has
eigenvalues `2cosh κ`, `2sinh κ`. Argued, not proved: read on the torus, each spin is a rigid slab spanning axes `0`,
`2`, `3`, so the coupling between neighbouring slabs is `K` times the slab volume. Along axis `1` the spectrum is the two transfer
eigenvalues. Along axes `0`, `2`, `3` the binomial expansion over subsets (`tunZ_expand`) writes `Z` as a sum of
`(slab volume)`-th powers of the levels `e^{K(2|t| − N)}`, `t ⊆ Fin N` with `N − |t|` even, each counted twice.

## What is proved

* `lineSpectrum_of_fintype`: a nonnegative spectrum with a top level, indexed by any finite type, is a `Top` spectrum
  indexed by `ℕ` with the same trace sequence.
* `tunZ_expand`: `Z(aM, N) = Σ_{q ∈ tunEven N} (tunLev a N q)^M`.
* `tunX_lineSpectral`: for `K ≥ 0`, `LineSpectral (tunX K)`.
* `spectralRep_of_lineSpectral`, `tunX_positive`: `LineSpectral` gives `DoublingRecursion.SpectralRep`, hence
  `Positive (tunX K)` through `DoublingRecursion.positive_of_rep`.
* `mixed_tunX_neg`: at `K = log 2` and `v = (0, 2, 0, 0)`, `mixed (tunX (log 2)) 0 1 v < 0`. The four partition
  functions are `Z(1,4) = 353/8`, `Z(2,4) = 67073/128`, `Z(1,8) = 198593/128`, `Z(2,8) = 4769324033/32768`, and
  `Z(2,8) Z(1,4)^4 < Z(2,4)^2 Z(1,8)^2`. Computed outside Lean: the ratio is about `0.83`, so `mixed ≈ −0.18`.
* `not_transverseDouble_tunX`: `¬ TransverseDouble (tunX (log 2))`.
* `not_transverseDouble_of_lineSpectral`: (T) is not a consequence of `LineSpectral` and `Positive` together.

## The mechanism (argued, not proved)

`x = N log(2cosh κ) + log(1 + tanh(κ)^N)`. The first term has the form `L_ν h(L_μ)` and cancels exactly in `mixed`,
with the bulk free energy. What remains is the tunnelling term `g = log(1 + tanh(κ)^N)` between the two ordered
states. Heuristically, a transverse doubling of the slab (`κ ↦ 2κ`) increases the correlation length along axis `1`, so it moves
`tanh(κ)^N` from near `0` towards `1`. With `g(1,·) ≈ 0` and `q = tanh(2κ)^N`, `mixed ≈ log(1+q²) − 2 log(1+q) < 0`.
A transverse doubling then raises the directional count along axis `1` by more than a factor of two. Nothing in this
section is a Lean statement; the proved fact is `mixed_tunX_neg` at one corner. The model defines `x` by its closed form; that it is the Ising ring is stated in the docstrings, not proved.

## The Wilson torus (argued, exact finite computation; not proved here)

For the gauge group `Z_2` with base side `n = 1`, the Wilson torus with sides `(2^a, 2^b, 1, 1)` splits exactly. A
link of a side-`1` direction `ρ` enters the `(μ, ρ)` plaquette as `U_ρ(x+e_μ) U_ρ(x)`, so the two side-`1` directions
carry two independent Ising models on the `2^a × 2^b` torus at coupling `2β` (each plaquette is counted in both
orientations in `RectWilson.rbd`), and the `(0,1)` plaquettes carry the two-dimensional `Z_2` gauge theory,
`Z ∝ 1 + tanh(2β)^{2^{a+b}}`. The split was checked against direct enumeration of every link configuration on the tori
`(1,2,1,1)`, `(2,1,1,1)` (two sites, `2^8`) and `(2,2,1,1)`, `(1,4,1,1)` (four sites, `2^{16}`). Exact transfer-matrix traces of the Ising parts then give
`mixed(xWG Z₂ 1 β) 0 1 (0,2,0,0) ≈ −0.29` at `β = 1/4`, negative for `β` between about `0.1` and `0.3`, and negative at
`(0,3,0,0)`, `(1,2,0,0)`, `(1,3,0,0)` in nearby windows. The same failure appears in the plain two-dimensional Ising
model on anisotropic tori (aspect ratio at least `4`) near and below the critical coupling. Square tori and the
weak- and strong-coupling ends give `mixed > 0`. The tree has no `GaugeGroup` instance for `Z_2`, so none of this is a
Lean statement.

## What does not follow

* Nothing here is a statement about `xWG G n β` for any group: `tunX` is an abstract corner function. It refutes (T) as
  a consequence of the one-axis spectral facts, not (T) for the Wilson torus.
* For `SU(N)` and even `n ≥ 2` (the range of `DoublingWilsonG.positiveG`), (T) is neither proved nor refuted.
* The free Gaussian field satisfies (T) (argued: `mixed = 4 Σ` over closed walks of odd winding in both directions,
  each with a positive weight). The Ising and `Z_2` computations (outside Lean) indicate that more than
  `LineSpectral` and `Positive` is needed.
* `not_transverseDouble_of_lineSpectral` strengthens `AxisSplit.not_transverseDouble`: that counterexample (`chiX`) is
  not line-spectral, while `tunX` is.

CHOSEN: `K = log 2` and `v = (0, 2, 0, 0)`, the first dyadic corner at which the rational values give `mixed < 0`;
`β = 1/4` the coupling quoted for the `Z_2` torus.
COMPUTED: `353/8`, `67073/128`, `198593/128`, `4769324033/32768`, `0.83`, `−0.18`, `−0.29`; the windows `0.1`–`0.3` and
the aspect ratio `4` are read from exact transfer traces, outside Lean. DERIVED: `3` the last direction label of
`Fin 4`; `8 = 2³` the length `2^{u_1}` at `u_1 = 3`; in `2^8` and `2^{16}`, `8 = 2 · 4` and `16 = 4 · 4` the links of a
two-site and a four-site torus, one bit each.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.TransverseTunnel

open Finset MassGap.DoublingRecursion MassGap.CasimirStep MassGap.AxisSplit

/-! ## 0. Spectra over a finite index -/

/-- **A finite-type spectrum is an `ℕ`-indexed `Top` spectrum.** DERIVED: `0` the sign. -/
theorem lineSpectrum_of_fintype {α : Type} [Fintype α] [DecidableEq α] (S : Finset α) (f : α → ℝ) (a₀ : α)
    (hmem : a₀ ∈ S) (hpos : 0 < f a₀) (hnn : ∀ a ∈ S, 0 ≤ f a) (hle : ∀ a ∈ S, f a ≤ f a₀) :
    ∃ (s : Finset ℕ) (w : ℕ → ℝ) (i₀ : ℕ), Top s w i₀ ∧ ∀ M : ℕ, powSum s w M = ∑ a ∈ S, f a ^ M := by
  let e := Fintype.equivFin α
  let ι : α ↪ ℕ := ⟨fun a => ((e a : Fin _) : ℕ), fun a b h => e.injective (Fin.ext h)⟩
  let w : ℕ → ℝ := fun i => if h : i < Fintype.card α then f (e.symm ⟨i, h⟩) else 0
  have hw : ∀ a, w (ι a) = f a := by
    intro a
    have hlt : ((e a : Fin _) : ℕ) < Fintype.card α := (e a).isLt
    simp only [w, ι, Function.Embedding.coeFn_mk, dif_pos hlt, Fin.eta, Equiv.symm_apply_apply]
  refine ⟨S.map ι, w, ι a₀, ⟨mem_map_of_mem ι hmem, by rw [hw]; exact hpos, ?_, ?_⟩, fun M => ?_⟩
  · intro i hi
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hi
    rw [hw]; exact hnn a ha
  · intro i hi
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hi
    rw [hw, hw]; exact hle a ha
  · unfold powSum
    rw [sum_map]
    simp only [hw]

/-- **`LineSpectral` gives `SpectralRep`**: the first three points of each line. DERIVED: `0`, `1`, `2` the points;
`2` the doubling. -/
theorem spectralRep_of_lineSpectral {x : Pt → ℝ} (hx : LineSpectral x) : SpectralRep x := by
  intro μ v
  obtain ⟨s, w, i₀, m, hT, hl⟩ := hx μ v
  have h0 := hl 0
  have h1 := hl 1
  have h2 := hl 2
  simp only [zero_smul, add_zero, pow_zero, one_mul, one_smul, pow_one] at h0 h1 h2
  rw [two_smul, ← add_assoc, show 2 ^ 2 * m = 2 * (2 * m) by ring] at h2
  exact ⟨ℕ, inferInstance, s, w, i₀, m, hT, h0, h1, h2⟩

/-! ## 1. The model -/

/-- `e^κ + e^{−κ}`, the even transfer eigenvalue. DERIVED: no numeral. -/
def tunCp (κ : ℝ) : ℝ := Real.exp κ + Real.exp (-κ)

/-- `e^κ − e^{−κ}`, the odd transfer eigenvalue. DERIVED: no numeral. -/
def tunCm (κ : ℝ) : ℝ := Real.exp κ - Real.exp (-κ)

/-- The Ising ring of `N` spins at coupling `κ`: `Tr` of the `N`-th power of the transfer. DERIVED: no numeral. -/
def tunZ (κ : ℝ) (N : ℕ) : ℝ := tunCp κ ^ N + tunCm κ ^ N

/-- The slab exponent: the doublings of axes `0`, `2`, `3`. DERIVED: `0`, `2`, `3` the slab directions. -/
def tunSlab (u : Pt) : ℕ := u 0 + u 2 + u 3

/-- **The corner function.** DERIVED: `2` the doubling; `1` the ring axis. -/
def tunX (K : ℝ) (u : Pt) : ℝ := Real.log (tunZ (K * 2 ^ tunSlab u) (2 ^ u 1))

/-- The levels along a slab axis: subsets `t ⊆ Fin N` with `N − |t|` even, each with two copies. DERIVED: `2` the
parity. -/
def tunEven (N : ℕ) : Finset (Finset (Fin N) × Bool) := univ.filter fun q => Even (N - q.1.card)

/-- The level `e^{a(2|t| − N)}`. DERIVED: `2` the two spins of a flip. -/
def tunLev (a : ℝ) (N : ℕ) (q : Finset (Fin N) × Bool) : ℝ := Real.exp (a * (2 * (q.1.card : ℝ) - N))

theorem tunCp_pos (κ : ℝ) : 0 < tunCp κ := by unfold tunCp; positivity

theorem tunCm_nonneg {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ tunCm κ := by
  unfold tunCm
  have : Real.exp (-κ) ≤ Real.exp κ := Real.exp_le_exp.mpr (by linarith)
  linarith

theorem tunCm_le_tunCp (κ : ℝ) : tunCm κ ≤ tunCp κ := by
  unfold tunCm tunCp
  have := Real.exp_pos (-κ)
  linarith

/-- **The binomial expansion over subsets.** DERIVED: `1` the sign of an even parity; `2` the copies. -/
theorem tunZ_expand (a : ℝ) (N M : ℕ) :
    tunZ (a * M) N = ∑ q ∈ tunEven N, tunLev a N q ^ M := by
  have key : ∀ t : Finset (Fin N), Real.exp (a * M) ^ t.card * Real.exp (-(a * M)) ^ (N - t.card)
      = Real.exp (a * (2 * (t.card : ℝ) - N)) ^ M := by
    intro t
    have hk : t.card ≤ N := by simpa using t.card_le_univ
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, Nat.cast_sub hk]
    congr 1
    ring
  have hp : tunCp (a * M) ^ N = ∑ t : Finset (Fin N),
      Real.exp (a * M) ^ t.card * Real.exp (-(a * M)) ^ (N - t.card) := by
    have h1 : tunCp (a * M) ^ N = ∏ _i : Fin N, (Real.exp (a * M) + Real.exp (-(a * M))) := by
      rw [prod_const, card_univ, Fintype.card_fin]
      rfl
    rw [h1, Fintype.prod_add]
    refine sum_congr rfl fun t _ => ?_
    rw [prod_const, prod_const, card_compl, Fintype.card_fin]
  have hm : tunCm (a * M) ^ N = ∑ t : Finset (Fin N),
      (-1) ^ (N - t.card) * (Real.exp (a * M) ^ t.card * Real.exp (-(a * M)) ^ (N - t.card)) := by
    have h1 : tunCm (a * M) ^ N = ∏ _i : Fin N, (Real.exp (a * M) + -Real.exp (-(a * M))) := by
      rw [prod_const, card_univ, Fintype.card_fin, tunCm, sub_eq_add_neg]
    rw [h1, Fintype.prod_add]
    refine sum_congr rfl fun t _ => ?_
    rw [prod_const, prod_const, card_compl, Fintype.card_fin, neg_pow]
    ring
  rw [tunZ, hp, hm, ← sum_add_distrib, tunEven, sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun t _ => ?_
  rw [Fintype.sum_bool]
  simp only [tunLev]
  rw [← key t]
  rcases Nat.even_or_odd (N - t.card) with h | h
  · rw [h.neg_one_pow, if_pos h]
    ring
  · rw [h.neg_one_pow, if_neg (Nat.not_even_iff_odd.mpr h)]
    ring

/-- A point of a dyadic line. DERIVED: `0`, `1` the entries of a unit vector. -/
theorem line_apply (v : Pt) (j : ℕ) (μ i : Fin 4) : (v + j • E μ) i = v i + if i = μ then j else 0 := by
  simp [E_apply]

/-- **The model is line-spectral.** DERIVED: `0`, `1` the level labels and the ring axis; `2` the doubling. -/
theorem tunX_lineSpectral {K : ℝ} (hK : 0 ≤ K) : LineSpectral (tunX K) := by
  intro μ v
  by_cases hμ : μ = 1
  · subst hμ
    set κ := K * 2 ^ tunSlab v with hκdef
    have hκ : 0 ≤ κ := by positivity
    refine ⟨{0, 1}, fun i => if i = 0 then tunCp κ else tunCm κ, 0, 2 ^ v 1,
      ⟨by simp, by simp [tunCp_pos], ?_, ?_⟩, fun j => ?_⟩
    · intro i _
      split_ifs
      · exact (tunCp_pos κ).le
      · exact tunCm_nonneg hκ
    · intro i _
      by_cases h : i = 0
      · simp [h]
      · simp [h, tunCm_le_tunCp]
    · have hs : tunSlab (v + j • E 1) = tunSlab v := by
        simp only [tunSlab, line_apply]; simp
      have h1 : (v + j • E 1) 1 = v 1 + j := by
        simp only [line_apply]; simp
      have he : 2 ^ (v 1 + j) = 2 ^ j * 2 ^ v 1 := by rw [pow_add, mul_comm]
      rw [tunX, hs, h1, ← hκdef, powSum, sum_pair (by norm_num), he]
      simp [tunZ]
  · set a := K * 2 ^ tunSlab v with hadef
    set N := 2 ^ v 1 with hNdef
    have ha : 0 ≤ a := by positivity
    have hlev : ∀ q ∈ tunEven N, tunLev a N q ≤ tunLev a N (univ, false) := by
      intro q _
      unfold tunLev
      refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ ha)
      have : (q.1.card : ℝ) ≤ N := by exact_mod_cast (by simpa using q.1.card_le_univ)
      simp only [card_univ, Fintype.card_fin]
      linarith
    obtain ⟨s, w, i₀, hT, hp⟩ := lineSpectrum_of_fintype (tunEven N) (tunLev a N) (univ, false)
      (by simp [tunEven]) (Real.exp_pos _) (fun _ _ => (Real.exp_pos _).le) hlev
    refine ⟨s, w, i₀, 1, hT, fun j => ?_⟩
    have hs : tunSlab (v + j • E μ) = tunSlab v + j := by
      simp only [tunSlab, line_apply]
      fin_cases μ <;> simp at hμ ⊢ <;> omega
    have h1 : (v + j • E μ) 1 = v 1 := by
      rw [line_apply, if_neg (Ne.symm hμ), add_zero]
    have hk : K * (2 : ℝ) ^ (tunSlab v + j) = a * ((2 ^ j * 1 : ℕ) : ℝ) := by
      rw [hadef]; push_cast; rw [pow_add]; ring
    rw [tunX, hs, h1, ← hNdef, hk, tunZ_expand, hp]

/-- **The model is positive.** DERIVED: no numeral. -/
theorem tunX_positive {K : ℝ} (hK : 0 ≤ K) : Positive (tunX K) :=
  positive_of_rep (spectralRep_of_lineSpectral (tunX_lineSpectral hK))

/-! ## 2. The transverse doubling fails -/

/-- `e^{log 2 · 2^k} = 2^{2^k}`. DERIVED: `2` the base. -/
theorem exp_log_two_mul (k : ℕ) : Real.exp (Real.log 2 * 2 ^ k) = 2 ^ 2 ^ k := by
  have : Real.log 2 * 2 ^ k = ((2 ^ k : ℕ) : ℝ) * Real.log 2 := by push_cast; ring
  rw [this, Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- The ring at the slab coupling `log 2 · 2^k`. DERIVED: `2` the base. -/
theorem tunZ_log_two (k N : ℕ) :
    tunZ (Real.log 2 * 2 ^ k) N = (2 ^ 2 ^ k + (2 ^ 2 ^ k)⁻¹) ^ N + (2 ^ 2 ^ k - (2 ^ 2 ^ k)⁻¹) ^ N := by
  rw [tunZ, tunCp, tunCm, Real.exp_neg, exp_log_two_mul]

/-- **The mixed difference is negative at `K = log 2`, `v = (0,2,0,0)`.** CHOSEN: `K = log 2`, `v`. COMPUTED: the
four values in the module docstring. DERIVED: `3` the ring doubling exponent at `v + e_1`. -/
theorem mixed_tunX_neg : mixed (tunX (Real.log 2)) 0 1 ![0, 2, 0, 0] < 0 := by
  have e11 : (![0, 2, 0, 0] : Pt) + E 0 + E 1 = ![1, 3, 0, 0] := by decide
  have e10 : (![0, 2, 0, 0] : Pt) + E 0 = ![1, 2, 0, 0] := by decide
  have e01 : (![0, 2, 0, 0] : Pt) + E 1 = ![0, 3, 0, 0] := by decide
  have val : ∀ (u : Pt) (k N : ℕ), tunSlab u = k → u 1 = N →
      tunX (Real.log 2) u = Real.log ((2 ^ 2 ^ k + (2 ^ 2 ^ k)⁻¹) ^ 2 ^ N + (2 ^ 2 ^ k - (2 ^ 2 ^ k)⁻¹) ^ 2 ^ N) := by
    intro u k N hk hN
    rw [tunX, hk, hN, tunZ_log_two]
  have v11 : tunX (Real.log 2) ![1, 3, 0, 0] = Real.log (4769324033 / 32768) := by
    rw [val _ 1 3 (by decide) (by decide)]; norm_num
  have v10 : tunX (Real.log 2) ![1, 2, 0, 0] = Real.log (67073 / 128) := by
    rw [val _ 1 2 (by decide) (by decide)]; norm_num
  have v01 : tunX (Real.log 2) ![0, 3, 0, 0] = Real.log (198593 / 128) := by
    rw [val _ 0 3 (by decide) (by decide)]; norm_num
  have v00 : tunX (Real.log 2) ![0, 2, 0, 0] = Real.log (353 / 8) := by
    rw [val _ 0 2 (by decide) (by decide)]; norm_num
  unfold mixed
  rw [e11, e10, e01, v11, v10, v01, v00]
  have hlt : (4769324033 / 32768 : ℝ) * (353 / 8) ^ 4 < (67073 / 128) ^ 2 * (198593 / 128) ^ 2 := by norm_num
  have hl := Real.log_lt_log (by positivity) hlt
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow] at hl
  push_cast at hl
  linarith

/-- **(T) fails for the model.** DERIVED: `0`, `1` the directions. -/
theorem not_transverseDouble_tunX : ¬ TransverseDouble (tunX (Real.log 2)) := by
  intro h
  have := (transverseDouble_iff _).mp h 0 1 ![0, 2, 0, 0] (by decide)
  linarith [mixed_tunX_neg]

/-- **(T) is not a consequence of line spectra and positivity.** DERIVED: `2` the base of `log 2`. -/
theorem not_transverseDouble_of_lineSpectral :
    ¬ ∀ x : Pt → ℝ, LineSpectral x → Positive x → TransverseDouble x := by
  intro h
  have hK : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  exact not_transverseDouble_tunX (h _ (tunX_lineSpectral hK) (tunX_positive hK))

end MassGap.TransverseTunnel

end

#print axioms MassGap.TransverseTunnel.lineSpectrum_of_fintype
#print axioms MassGap.TransverseTunnel.spectralRep_of_lineSpectral
#print axioms MassGap.TransverseTunnel.tunZ_expand
#print axioms MassGap.TransverseTunnel.tunX_lineSpectral
#print axioms MassGap.TransverseTunnel.tunX_positive
#print axioms MassGap.TransverseTunnel.mixed_tunX_neg
#print axioms MassGap.TransverseTunnel.not_transverseDouble_tunX
#print axioms MassGap.TransverseTunnel.not_transverseDouble_of_lineSpectral
