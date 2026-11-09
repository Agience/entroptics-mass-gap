import Mathlib
import MassGap.PeriodicState

/-!
# MassGap.PeriodicDyadic — the dyadic extent filter, and why `dvdFilter` cannot carry it

`PeriodicState.periodicUltra` is chosen finer than `PeriodicState.dyadicFilter` (power-of-two extents).

* `not_pow2Set_mem` — no filter finer than `PeriodicState.dvdFilter` contains `pow2Set` (the extents
  divisible by `3` are eventually forced there, and no power of two is). Along a `dvdFilter`
  ultrafilter the doubling family `{2^k n}` would be invisible.
* `dyadic_freq_cells` — cells of power-of-two side are frequent along `dyadicFilter`.
* `dyadic_seed_mem`, `periodicUltra_seed_mem` — the doubling family of a power-of-two seed `2^{a+1}`
  is a set of `dyadicFilter`, hence of `periodicUltra hN β` at every `β`.
-/

namespace MassGap.PeriodicDyadic

open Filter MassGap.PeriodicState

/-- **The clash.** No filter finer than `dvdFilter` and not `⊥` contains `pow2Set`. -/
theorem not_pow2Set_mem {u : Filter ℕ} [u.NeBot] (hu : u ≤ PeriodicState.dvdFilter) :
    pow2Set ∉ u := by
  intro hmem
  have h3 : PeriodicState.dvdSet (2, 0) ∈ u :=
    hu (Filter.mem_iInf_of_mem (2, 0) (Filter.mem_principal_self _))
  obtain ⟨j, hj1, hj2⟩ := Filter.nonempty_of_mem (Filter.inter_mem hmem h3)
  obtain ⟨k, hk⟩ := hj1
  have hdvd : 3 ∣ 2 ^ k := by rw [← hk]; exact hj2.1
  have : 3 ∣ 2 := (Nat.prime_three.dvd_of_dvd_pow hdvd)
  omega

/-- **Cells of power-of-two side are frequent along `dyadicFilter`**: the cells `2^b * m - 1`,
`m ≥ M₀`, form a set of `dyadicFilter`. -/
theorem dyadic_freq_cells (b M₀ : ℕ) :
    (fun m => 2 ^ b * m - 1) '' Set.Ici M₀ ∈ dyadicFilter := by
  filter_upwards [dyadic_dvd_pow (b + 1),
    (eventually_ge_atTop (2 ^ b * M₀)).filter_mono dyadicFilter_le_atTop] with j hj hjM
  have e : 2 * j + 2 = 2 * (j + 1) := by ring
  rw [e, pow_succ, mul_comm (2 ^ b) 2] at hj
  obtain ⟨m, hm⟩ := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) hj
  have hb : 0 < 2 ^ b := Nat.two_pow_pos b
  refine ⟨m, ?_, ?_⟩
  · show M₀ ≤ m
    refine Nat.le_of_mul_le_mul_left ?_ hb
    omega
  · show 2 ^ b * m - 1 = j
    omega

/-- **The doubling family of a power-of-two seed is a set of `dyadicFilter`.** -/
theorem dyadic_seed_mem (a : ℕ) :
    {j | ∃ k : ℕ, 2 * j + 2 = 2 ^ k * 2 ^ (a + 1)} ∈ dyadicFilter := by
  have h1 : ∀ᶠ j in dyadicFilter, 2 ^ (a + 1) ≤ 2 * j + 2 :=
    ((eventually_ge_atTop (2 ^ (a + 1))).filter_mono dyadicFilter_le_atTop).mono fun j hj => by omega
  have h2 : ∀ᶠ j in dyadicFilter, j ∈ pow2Set := mem_inf_of_right (mem_principal_self _)
  filter_upwards [h1, h2] with j hj ⟨k, hk⟩
  rw [hk] at hj
  have hka : a + 1 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp hj
  refine ⟨k - (a + 1), ?_⟩
  rw [hk, ← pow_add, Nat.sub_add_cancel hka]

/-- **The doubling family of a power-of-two seed lies in `periodicUltra`.** -/
theorem periodicUltra_seed_mem {N : ℕ} (hN : N ≠ 0) (β : ℝ) (a : ℕ) :
    {j | ∃ k : ℕ, 2 * j + 2 = 2 ^ k * 2 ^ (a + 1)}
      ∈ ((periodicUltra (N := N) hN β : Ultrafilter ℕ) : Filter ℕ) :=
  periodicUltra_le_dyadic hN β (dyadic_seed_mem a)

#print axioms not_pow2Set_mem
#print axioms dyadic_freq_cells
#print axioms dyadic_seed_mem

end MassGap.PeriodicDyadic
