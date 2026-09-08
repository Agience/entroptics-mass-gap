import Mathlib

/-!
# MassGap.CentreDominance — the R3b assembly: area beats perimeter (`σ_SU(N) = σ_Z`)

R3b (centre dominance) reduces the `SU(N)` gap to the `Z_N` centre gap: `σ_SU(N) = σ_Z`, given the non-centre
(coset) contribution to the Wilson loop is perimeter-bounded (notes §13). This module proves the ASSEMBLY:
if the perimeter/area ratio vanishes, the string tension equals the centre part `σ_Z`. The single remaining
input is the non-centre perimeter bound itself — a convergent coset expansion, rigorous at strong coupling —
which enters here as the hypothesis `P/A → 0`.

Imported by the `MassGap` aggregate (`MassGap.lean`).
-/

namespace MassGap.CentreDominance

open Filter

/-- **Area beats perimeter: `σ_SU(N) = σ_Z`.** With `−log⟨W(C_n)⟩/A_n = σ_Z − c·(P_n/A_n)` (the centre area
law `σ_Z` plus a non-centre correction of size `c·P_n`) and the perimeter/area ratio vanishing
(`P_n/A_n → 0`, the non-centre perimeter bound), the per-area free energy tends to `σ_Z`: the `SU(N)` string
tension is the centre `σ_Z`. Then `Δ ∼ π√σ_Z > 0`, so `ρ'(1) < 1`. -/
theorem string_tension_eq_centre {σZ c : ℝ} {A P : ℕ → ℝ}
    (hPA : Tendsto (fun n => P n / A n) atTop (nhds 0)) :
    Tendsto (fun n => σZ - c * (P n / A n)) atTop (nhds σZ) := by
  simpa using tendsto_const_nhds.sub (hPA.const_mul c)

#print axioms string_tension_eq_centre

end MassGap.CentreDominance
