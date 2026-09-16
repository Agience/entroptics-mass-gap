import Mathlib

/-!
# C-1: the crossover tension from a bounded correlation moment (the analytic half, machine-checked)

The min-entropy tension the gap reads is `μ = log(S(0)/S(2π/L))` of the whitened :F²: correlation, where
`S(k) = Σ_d ρ(d) cos(2πkd/L)`. With reflection positivity (`ρ ≥ 0`, so `λ₁ = S(0)` and `λ₂ ≥ S(2π/L)`,
`FreeField.structure_factor_peak_at_zero`), `μ ≤ log(S(0)/S(2π/L)) = -log ⟨cos θ⟩_ρ`. This module proves the
purely analytic step that turns a **bounded correlation second moment** into confinement `μ < κ₀`:

    ⟨cos θ⟩_ρ ≥ 1 - ⟨θ²⟩_ρ/2   (cos x ≥ 1 - x²/2),   and   ⟨cos θ⟩ > 3^{-1/4} ⟹ -log⟨cos θ⟩ < ¼log3 = κ₀,

so `μ < κ₀` whenever `⟨θ²⟩_ρ/2 < 1 - 3^{-1/4}`, i.e. `M₂ < (1-3^{-1/4})L²/(2π²)` (a bounded correlation
length). This is the machine-checked half of C-1; the measured input — that the :F²: correlation moment IS bounded
across the crossover (finite specific heat / SU(N) no bulk transition) — is the cited physical content
.

## THE APERTURE POSTULATE — an assumption of this program, stated rather than smuggled

The read factors into a window part and a substrate part:

    ⟨cos θ⟩ ≥ 1 − (2π/(N+1))² · ⟨dist²⟩ / 2      (`Read.cos_avg_ge_circ`)

where `dist` is the separation ON THE CIRCLE of `N+1` sites (`circLag`). That bound is a theorem and
needs no assumption. What this program ASSUMES is how to READ its two factors:

  * `(2π/(N+1))²` is the **aperture** — the finite, discrete window the measurement is taken through.
  * `⟨dist²⟩` is a property of the **substrate**, carrying no reference to the window.

IT MUST BE THE CIRCLE DISTANCE. `thetaMoment_eq` gives the same factorisation with the RAW lag index,
`⟨θ²⟩ = (2π/(N+1))²⟨d²⟩`, and that version is useless. On a periodic extent the correlation obeys
`ρ(N) = ρ(−1) = ρ(1)`, so weighting the far half of the lag range by `d²` makes the moment grow like
`N²` even when the correlation length is FIXED — for `ρ(d) = e^{−dist/1.5}` the raw moment runs
14.5, 68.9, 307, 1305, 5384 across extents 8 to 128, while the circle moment settles at 3.28. A
hypothesis bounding the raw moment is satisfiable by no physical correlation at all, gapped or not.
`cos` is even and 2π-periodic, so the read never saw the raw index in the first place
(`Read.cos_theta_circ`); using it was a bookkeeping error, not a modelling choice.
  * `κ₀ = ¼log3` also belongs to the substrate: `Floor.lean` derives it by counting directed cube
    paths (`3^k` of them) as an `n → ∞` per-area density, with no aperture in it anywhere.

So the gap statement `μ < κ₀` is a comparison ACROSS these two ledgers: an aperture-suppressed
reading against a substrate density. The margin grows like the aperture squared because that is the
exchange rate between the books, not because anything physical changes.

WHY IT IS AN ASSUMPTION AND NOT A THEOREM. Nothing here derives that `⟨d²⟩` is substrate-intrinsic;
that is an interpretive commitment about what the objects mean, and writing it as a Lean `axiom` would
manufacture a theorem out of an interpretation. It is recorded here in prose instead, so a reader can
reject it without having to reverse-engineer it from the definitions.

WHAT IT COSTS, AND HOW IT CAN FAIL. The postulate is not free: it predicts that `⟨d²⟩` is INVARIANT
under changing the aperture, for any theory whose substrate correlation is finite. That is testable
and is being tested — `⟨d²⟩` against a growing aperture, a gapped arm against a gapless one, matched
sampling. If both arms scale the same way, the factorisation carries no physics and this reading is
wrong.

THE ERROR IT NAMES. A quantity read off one aperture may not be set beside the same quantity read off
a different aperture without converting. This effort has made that mistake three times — `m_hi`
compared across unmatched sampling ratio, the clustering total `K` across unmatched couplings, and
`⟨d²⟩` itself across unmatched apertures — each time treating a measured value as a substrate fact.
Under this postulate those are one error, not three.
-/

namespace MassGap.Moment

open scoped BigOperators

/-- **The cos-moment bound.** For a probability vector `p` over a finite index and angles `θ`, the
`p`-average of `cos θ` is at least `1 - ⟨θ²⟩/2` (termwise `cos x ≥ 1 - x²/2`). -/
theorem cos_avg_ge {ι : Type*} [Fintype ι] (p θ : ι → ℝ)
    (hp : ∀ d, 0 ≤ p d) (hsum : ∑ d, p d = 1) :
    1 - (∑ d, p d * (θ d) ^ 2) / 2 ≤ ∑ d, p d * Real.cos (θ d) := by
  have key : ∑ d, p d * (1 - (θ d) ^ 2 / 2) ≤ ∑ d, p d * Real.cos (θ d) :=
    Finset.sum_le_sum fun d _ =>
      mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos) (hp d)
  have hpt : ∀ d, p d * (1 - (θ d) ^ 2 / 2) = p d - p d * (θ d) ^ 2 / 2 := fun d => by ring
  have expand : ∑ d, p d * (1 - (θ d) ^ 2 / 2) = 1 - (∑ d, p d * (θ d) ^ 2) / 2 := by
    rw [Finset.sum_congr rfl (fun d _ => hpt d), Finset.sum_sub_distrib, hsum, ← Finset.sum_div]
  rwa [expand] at key

/-- **-log of a value above `3^{-1/4}` is below the floor `κ₀ = ¼log3`.** -/
theorem neg_log_lt_floor {c : ℝ} (hc : (3 : ℝ) ^ (-(1 : ℝ) / 4) < c) :
    - Real.log c < (1 / 4) * Real.log 3 := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hlog : Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4)) = -(1 / 4) * Real.log 3 := by
    rw [Real.log_rpow (by norm_num)]; ring
  have hmono : Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4)) < Real.log c := Real.log_lt_log h3 hc
  rw [hlog] at hmono
  linarith

/-- **The crossover tension is below the floor from a bounded moment (the analytic half of C-1).**
If the `p`-weighted angular second moment satisfies `⟨θ²⟩/2 < 1 - 3^{-1/4}`, then the min-entropy tension
`μ = -log ⟨cos θ⟩` is strictly below the entropy floor `κ₀ = ¼ log 3`. Combined with reflection positivity
(`μ ≤ -log⟨cos θ⟩`, `λ₁=S(0)`, `λ₂ ≥ S(2π/L)`) this is `μ < κ₀`; the measured input is that the moment IS bounded
(finite correlation length / no bulk transition), the cited physical content. -/
theorem tension_lt_floor_of_moment {ι : Type*} [Fintype ι] (p θ : ι → ℝ)
    (hp : ∀ d, 0 ≤ p d) (hsum : ∑ d, p d = 1)
    (hmom : (∑ d, p d * (θ d) ^ 2) / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    - Real.log (∑ d, p d * Real.cos (θ d)) < (1 / 4) * Real.log 3 := by
  have hcavg := cos_avg_ge p θ hp hsum
  have hc_gt : (3 : ℝ) ^ (-(1 : ℝ) / 4) < ∑ d, p d * Real.cos (θ d) := by
    have h1 : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 - (∑ d, p d * (θ d) ^ 2) / 2 := by linarith
    linarith
  exact neg_log_lt_floor hc_gt

/-! ## The concrete entropy-matched read: `μ`, `p`, `θ` derived from a nonnegative correlation

A translation-invariant whitened correlation `ρ ≥ 0` over the lag index determines the read outright: the
probability vector `p = ρ/Σρ`, the angles `θ_d = 2π d /(N+1)`, and the min-entropy tension
`μ = -log ⟨cos θ⟩_p = log(S(0)/S(2π/N))`. So `p`'s vector properties and the tension identity are
THEOREMS; the only inputs are `ρ ≥ 0` (reflection positivity) and the bounded moment (finite
correlation length / no bulk transition). -/

/-- A concrete entropy-matched read: a whitened, translation-invariant correlation `ρ ≥ 0` over the lag
index, with positive total mass. Everything the gap uses (`p`, `θ`, the tension `μ`) is derived from it. -/
structure Read (N : ℕ) where
  ρ : Fin (N + 1) → ℝ
  hρ : ∀ d, 0 ≤ ρ d
  hpos : 0 < ∑ d, ρ d

/-- A read always exists (the flat correlation `ρ ≡ 1`), so any opaque ensemble data valued in `Read N` is
well-formed. (The proof's read is the concrete `Complete.readYMAt`.) -/
instance (N : ℕ) : Inhabited (Read N) where
  default :=
    { ρ := fun _ => 1
      hρ := fun _ => zero_le_one
      hpos := Finset.sum_pos (fun _ _ => one_pos) ⟨0, Finset.mem_univ 0⟩ }

namespace Read

variable {N : ℕ} (R : Read N)

/-- The correlation as a probability vector `p_d = ρ_d / Σρ`. -/
noncomputable def p (d : Fin (N + 1)) : ℝ := R.ρ d / ∑ d', R.ρ d'
/-- The lag angle `θ_d = 2π d /(N+1)` (the `k=1` structure-factor phase). Carries `R` so `R.θ` reads as a
field of the concrete read even though the angle depends only on the lattice index. -/
noncomputable def θ (_R : Read N) (d : Fin (N + 1)) : ℝ := 2 * Real.pi * (d : ℝ) / (N + 1)
/-- The min-entropy tension `μ = -log ⟨cos θ⟩_p = log(S(0)/S(2π/N))`. -/
noncomputable def tension : ℝ := - Real.log (∑ d, R.p d * Real.cos (R.θ d))

theorem p_nonneg (d : Fin (N + 1)) : 0 ≤ R.p d := div_nonneg (R.hρ d) R.hpos.le

theorem p_sum : ∑ d, R.p d = 1 := by
  unfold Read.p
  rw [← Finset.sum_div, div_self (ne_of_gt R.hpos)]

/-- **The concrete tension is below the floor from a bounded moment** (via `tension_lt_floor_of_moment`):
`μ = -log⟨cos θ⟩ < κ₀ = ¼log3` when `⟨θ²⟩/2 < 1 - 3^{-1/4}`. -/
theorem tension_lt_floor
    (hmom : (∑ d, R.p d * (R.θ d) ^ 2) / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    R.tension < (1 / 4) * Real.log 3 :=
  tension_lt_floor_of_moment R.p R.θ (fun d => R.p_nonneg d) R.p_sum hmom

/-- The lag angle squared factors the `1/L²` aperture scaling out of the lag index: `θ_d² = (2π/(N+1))² d²`. -/
theorem theta_sq (d : Fin (N + 1)) : (R.θ d) ^ 2 = (2 * Real.pi / (N + 1)) ^ 2 * (d : ℝ) ^ 2 := by
  unfold Read.θ; ring

/-- The angular second moment factors as `⟨θ²⟩ = (2π/(N+1))² ⟨d²⟩`: the correlation's angular spread is its
lag second moment (a squared correlation length) times the explicit `1/L²` aperture scaling. -/
theorem thetaMoment_eq :
    ∑ d, R.p d * (R.θ d) ^ 2 = (2 * Real.pi / (N + 1)) ^ 2 * ∑ d, R.p d * (d : ℝ) ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by rw [R.theta_sq d]; ring

end Read

/-- `3^(-1/4) < 1`, so the aperture condition has room on the right. -/
theorem floor_rhs_pos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have h : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  linarith

/-- The tension is nonnegative: `⟨cos θ⟩ ≤ 1` for a probability vector, so `−log⟨cos θ⟩ ≥ 0`. -/
theorem Read.tension_nonneg {N : ℕ} (R : Read N) : 0 ≤ R.tension := by
  have hcos : ∀ d, |R.p d * Real.cos (R.θ d)| ≤ R.p d := by
    intro d
    rw [abs_mul, abs_of_nonneg (R.p_nonneg d)]
    exact mul_le_of_le_one_right (R.p_nonneg d) (Real.abs_cos_le_one _)
  have habs : |∑ d, R.p d * Real.cos (R.θ d)| ≤ 1 :=
    le_trans (Finset.abs_sum_le_sum_abs _ _)
      (le_trans (Finset.sum_le_sum (fun d _ => hcos d)) (le_of_eq R.p_sum))
  have hlog : Real.log (∑ d, R.p d * Real.cos (R.θ d)) ≤ 0 := by
    rw [← Real.log_abs]; exact Real.log_nonpos (abs_nonneg _) habs
  show 0 ≤ - Real.log (∑ d, R.p d * Real.cos (R.θ d))
  linarith

/-- **The tension is below the floor exactly when the read's own cosine average clears `3^{-1/4}`.**

DERIVED, not a new hypothesis: `tension` is DEFINED as `-log ⟨cos θ⟩_p`, so this is the definitional
comparison and nothing more. It is stated because it is the route a measurement can certify. The
second-moment routes below reach the same conclusion through `1 - x²/2 ≤ cos x`, a SUFFICIENT
condition: they are what to use when the substrate is characterised by a correlation length, and
this is what to use when the ensemble is in hand. Certifying this needs ONE scalar -- the ratio
`S(2π/L)/S(0)` -- where the moment route needs every lag ratio separately. -/
theorem Read.tension_lt_floor_of_cosAvg {N : ℕ} (R : Read N)
    (hc : (3 : ℝ) ^ (-(1 : ℝ) / 4) < ∑ d, R.p d * Real.cos (R.θ d)) :
    R.tension < (1 / 4) * Real.log 3 :=
  neg_log_lt_floor hc

#print axioms Read.tension_lt_floor_of_cosAvg

/-- The contrapositive direction, so the two are known to be the same statement rather than one
implying the other: a tension below the floor forces the cosine average above `3^{-1/4}`, PROVIDED
the average is positive (a nonpositive average has no logarithm and the tension is not a read). -/
theorem Read.cosAvg_gt_of_tension_lt_floor {N : ℕ} (R : Read N)
    (hpos : 0 < ∑ d, R.p d * Real.cos (R.θ d))
    (h : R.tension < (1 / 4) * Real.log 3) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < ∑ d, R.p d * Real.cos (R.θ d) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hlog : Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4)) = -(1 / 4) * Real.log 3 := by
    rw [Real.log_rpow (by norm_num)]; ring
  have hlt : Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4)) < Real.log (∑ d, R.p d * Real.cos (R.θ d)) := by
    rw [hlog]
    have : R.tension = - Real.log (∑ d, R.p d * Real.cos (R.θ d)) := rfl
    rw [this] at h; linarith
  exact (Real.log_lt_log_iff h3 hpos).mp hlt

#print axioms Read.cosAvg_gt_of_tension_lt_floor

/-- The aperture factor `(2π/(N+1))²·B/2` tends to zero, at any fixed `B`. -/
theorem aperture_factor_tendsto_zero (B : ℝ) :
    Filter.Tendsto (fun N : ℕ => (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2)
      Filter.atTop (nhds 0) := by
  have hN : Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h0 : Filter.Tendsto (fun N : ℕ => 2 * Real.pi / ((N : ℝ) + 1)) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hN
  simpa using ((h0.pow 2).mul_const B).div_const 2

/-- The distance from lag `d` to the origin ON THE CIRCLE of `N+1` sites. -/
-- DERIVED: `N + 1` is the periodic extent the lag index runs over, so `N + 1 - d` is the same
-- separation measured the other way round the circle. Neither is a magnitude.
def circLag {N : ℕ} (d : Fin (N + 1)) : ℕ := min (d : ℕ) (N + 1 - (d : ℕ))

/-- **The lag angle sees only the circle distance.** `cos θ_d = cos(2π·circLag d/(N+1))`. -/
theorem Read.cos_theta_circ {N : ℕ} (R : Read N) (d : Fin (N + 1)) :
    Real.cos (R.θ d) = Real.cos (2 * Real.pi * (circLag d : ℝ) / (N + 1)) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rcases le_total ((d : ℕ)) (N + 1 - (d : ℕ)) with h | h
  · rw [circLag, min_eq_left h]; rfl
  · rw [circLag, min_eq_right h]
    have hd : ((N + 1 - (d : ℕ) : ℕ) : ℝ) = ((N : ℝ) + 1) - (d : ℕ) := by
      have hle : (d : ℕ) ≤ N + 1 := le_of_lt d.isLt
      push_cast [Nat.cast_sub hle]
      ring
    rw [hd]
    have : 2 * Real.pi * (((N : ℝ) + 1) - (d : ℕ)) / ((N : ℝ) + 1)
        = 2 * Real.pi - 2 * Real.pi * (d : ℕ) / ((N : ℝ) + 1) := by
      field_simp
    rw [this, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
    unfold Read.θ
    ring

/-- **The cos-moment bound on the circle, the OTHER way.** `cos_avg_ge_circ` bounds the cosine
average from BELOW by the circular second moment, which is the direction that lets a short
correlation length SATISFY the aperture condition. This bounds it from ABOVE, which is the direction
that lets the condition, once satisfied, SAY something.

The two use the two elementary bounds on cosine over one half-turn: `1 - x^2/2 <= cos x` there, and
`cos x <= 1 - (2/pi^2) x^2` here, the latter tight at both `x = 0` and `x = pi`. The hypothesis
`|x| <= pi` is not a restriction to check separately -- on the circle `circLag d <= (N+1)/2` by
construction, so the lag angle never leaves the half-turn where the bound holds.

DERIVED: `8` is `(2/pi^2) * (2 pi)^2`, the two constants of the cosine bound and the lag angle
multiplied out. Nothing is chosen. -/
theorem Read.cos_avg_le_circ {N : ℕ} (R : Read N) :
    ∑ d, R.p d * Real.cos (R.θ d)
      ≤ 1 - 8 / ((N : ℝ) + 1) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have key : ∀ d : Fin (N + 1),
      R.p d * Real.cos (R.θ d)
        ≤ R.p d * (1 - 8 / ((N : ℝ) + 1) ^ 2 * (circLag d : ℝ) ^ 2) := by
    intro d
    rw [R.cos_theta_circ d]
    refine mul_le_mul_of_nonneg_left ?_ (R.p_nonneg d)
    -- the lag angle never leaves the half-turn, because the lag never exceeds half the circle
    have hhalf : 2 * (circLag d) ≤ N + 1 := by
      have := d.isLt; unfold circLag; omega
    have hhalfR : 2 * (circLag d : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hhalf
    have hc0 : (0 : ℝ) ≤ (circLag d : ℝ) := Nat.cast_nonneg _
    have habs : |2 * Real.pi * (circLag d : ℝ) / ((N : ℝ) + 1)| ≤ Real.pi := by
      rw [abs_of_nonneg (by positivity)]
      rw [div_le_iff₀ hN]
      nlinarith [Real.pi_pos]
    have hcos := Real.cos_le_one_sub_mul_cos_sq habs
    have harith : 1 - 2 / Real.pi ^ 2 * (2 * Real.pi * (circLag d : ℝ) / ((N : ℝ) + 1)) ^ 2
        = 1 - 8 / ((N : ℝ) + 1) ^ 2 * (circLag d : ℝ) ^ 2 := by
      field_simp
      ring
    linarith [hcos, harith.le, harith.ge]
  have hsum := Finset.sum_le_sum (fun d (_ : d ∈ Finset.univ) => key d)
  have hexp : ∑ d, R.p d * (1 - 8 / ((N : ℝ) + 1) ^ 2 * (circLag d : ℝ) ^ 2)
      = 1 - 8 / ((N : ℝ) + 1) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2) := by
    have hpt : ∀ d : Fin (N + 1),
        R.p d * (1 - 8 / ((N : ℝ) + 1) ^ 2 * (circLag d : ℝ) ^ 2)
          = R.p d - 8 / ((N : ℝ) + 1) ^ 2 * (R.p d * (circLag d : ℝ) ^ 2) :=
      fun d => by ring
    rw [Finset.sum_congr rfl (fun d _ => hpt d), Finset.sum_sub_distrib, R.p_sum,
      ← Finset.mul_sum]
  linarith [hsum, hexp.le, hexp.ge]

#print axioms Read.cos_avg_le_circ

/-- **THE APERTURE CONDITION, MADE EXPLICIT.** A tension below the entropy floor does not merely
imply that *some* gap exists: it caps the SUBSTRATE RATIO -- the circular second moment of the lag
distribution, divided by the squared aperture -- at a number derived from the floor alone.

    μ < κ₀   ⟹   (∑ p(d) circLag(d)^2) / (N+1)^2  <  (1 - 3^{-1/4}) / 8  =  0.0300…

This is the converse of `tension_lt_floor_of_circ_moment`, which travels from a bounded moment to a
tension below the floor. Having both means the aperture condition and a bounded substrate ratio are
each other's consequences rather than one being a sufficient proxy for the other, and it is the
direction that turns a measured tension into a checkable number about the correlation.

The positivity hypothesis is the same one `cosAvg_gt_of_tension_lt_floor` carries and for the same
reason: a nonpositive cosine average has no logarithm, so the tension is not a read there at all.

DERIVED: `8` is the constant of `cos_avg_le_circ`; `3^{-1/4}` is `e^{-κ₀}` with `κ₀` proved in
`Floor.lean`. The bound is a composition of those two and contains nothing else. -/
theorem Read.substrate_lt_of_tension_lt_floor {N : ℕ} (R : Read N)
    (hpos : 0 < ∑ d, R.p d * Real.cos (R.θ d))
    (h : R.tension < (1 / 4) * Real.log 3) :
    (∑ d, R.p d * (circLag d : ℝ) ^ 2) / ((N : ℝ) + 1) ^ 2
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8 := by
  have hN : (0 : ℝ) < ((N : ℝ) + 1) ^ 2 := by positivity
  set S : ℝ := ∑ d, R.p d * (circLag d : ℝ) ^ 2 with hS
  have hgt := R.cosAvg_gt_of_tension_lt_floor hpos h
  have hle := R.cos_avg_le_circ
  -- the two squeeze the moment from both sides: floor < cosAvg <= 1 - 8 S / (N+1)^2
  have hkey : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 - 8 / ((N : ℝ) + 1) ^ 2 * S :=
    lt_of_lt_of_le hgt hle
  have hfrac : (8 * S) / ((N : ℝ) + 1) ^ 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
    have : 8 / ((N : ℝ) + 1) ^ 2 * S = (8 * S) / ((N : ℝ) + 1) ^ 2 := by ring
    linarith [hkey, this.le, this.ge]
  have h8S : 8 * S < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * ((N : ℝ) + 1) ^ 2 :=
    (div_lt_iff₀ hN).mp hfrac
  rw [div_lt_div_iff₀ hN (by norm_num : (0 : ℝ) < 8)]
  linarith [h8S]

#print axioms Read.substrate_lt_of_tension_lt_floor
/-- **THE DIFFRACTION LIMIT, AS A THEOREM: a spread-out correlation cannot clear the floor.**

The contrapositive of `substrate_lt_of_tension_lt_floor`, and the mechanism the whole reading rests
on. A correlation whose circular second moment reaches the ceiling `(1 - 3^{-1/4})/8` has a tension AT
OR ABOVE the entropy floor: the screen cannot host it.

WHY THIS IS THE MASSLESS EXCLUSION. A free massless field on a periodic screen of `n` sites has its
lowest mode at `2π/n`, giving `ρ(d) = e^{-2π·circLag(d)/n}` and a substrate ratio of `0.0321808` —
computed in `code/certify/aperture_cap_of_floor.py`, constant in `n` to seven digits from `n = 64`
upward and rising to that value from below. The ceiling is `0.0300205`. The massless configuration
therefore exceeds it by a factor `1.072`, at EVERY aperture, and this theorem excludes it.

That is the diffraction limit stated arithmetically: a band-limited screen cannot carry the
infinitely-extended mode a gapless theory requires, because carrying it would put more of the
correlation's weight at large lag than the entropy floor permits. What the screen CAN carry is
therefore concentrated, and a concentrated correlation decays — at a positive rate, which is the gap.

THE MARGIN IS NOT TIGHT, AND THAT MATTERS. `(1 - 3^{-1/4})/8` comes from the elementary bound
`cos x ≤ 1 - (2/π²)x²`, which gives away a factor of `π²/4 = 2.467` against the exact criterion. The
exact criterion excludes the massless mode by the far wider margin `a⋆ = 1.7489` in the scaling
variable. So masslessness is excluded even after the lossy step — the conclusion does not depend on
the sharpness of the inequality used to reach it.

DERIVED: the ceiling is `(1 - e^{-κ₀})/8` with `κ₀` proved in `Floor.lean`; the `8` is the constant of
`cos_avg_le_circ`. Nothing is chosen, and the massless value is computed, not fitted. -/
theorem Read.tension_ge_floor_of_substrate {N : ℕ} (R : Read N)
    (hpos : 0 < ∑ d, R.p d * Real.cos (R.θ d))
    (hsub : (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8
      ≤ (∑ d, R.p d * (circLag d : ℝ) ^ 2) / ((N : ℝ) + 1) ^ 2) :
    ¬ (R.tension < (1 / 4) * Real.log 3) := by
  intro h
  exact absurd (R.substrate_lt_of_tension_lt_floor hpos h) (not_lt.mpr hsub)

#print axioms Read.tension_ge_floor_of_substrate


/-- **The cos-moment bound on the circle.** Sharper than `cos_avg_ge` composed with `thetaMoment_eq`,
and stated in the quantity a finite correlation length bounds. -/
theorem Read.cos_avg_ge_circ {N : ℕ} (R : Read N) :
    1 - (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2) / 2
      ≤ ∑ d, R.p d * Real.cos (R.θ d) := by
  have key : ∀ d : Fin (N + 1),
      R.p d * (1 - (2 * Real.pi * (circLag d : ℝ) / ((N : ℝ) + 1)) ^ 2 / 2)
        ≤ R.p d * Real.cos (R.θ d) := by
    intro d
    rw [R.cos_theta_circ d]
    exact mul_le_mul_of_nonneg_left Real.one_sub_sq_div_two_le_cos (R.p_nonneg d)
  have hsum := Finset.sum_le_sum (fun d (_ : d ∈ Finset.univ) => key d)
  have hexp : ∑ d, R.p d * (1 - (2 * Real.pi * (circLag d : ℝ) / ((N : ℝ) + 1)) ^ 2 / 2)
      = 1 - (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2) / 2 := by
    have hpt : ∀ d : Fin (N + 1),
        R.p d * (1 - (2 * Real.pi * (circLag d : ℝ) / ((N : ℝ) + 1)) ^ 2 / 2)
          = R.p d - (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * (R.p d * (circLag d : ℝ) ^ 2) / 2 :=
      fun d => by ring
    rw [Finset.sum_congr rfl (fun d _ => hpt d), Finset.sum_sub_distrib, R.p_sum]
    congr 1
    rw [← Finset.sum_div, ← Finset.mul_sum]
  rwa [hexp] at hsum

/-- **Confinement from a bounded CIRCLE moment** — the hypothesis a gapped theory can actually
satisfy. The moment is taken about `circLag`, the separation on the circle, and not about the raw lag
index: on a periodic extent the far half of the lag range is the near half reflected, so a raw-index
moment grows like `N²` at any FIXED correlation length and no physical correlation bounds it
uniformly in the aperture. A raw bound is the stronger hypothesis and implies this one
(`Complete.circ_moment_le_lag_moment`), which is how the grid certificates feed this route. -/
theorem Read.tension_lt_floor_of_circ_moment {N : ℕ} (R : Read N) {B : ℝ}
    (hB : ∑ d, R.p d * (circLag d : ℝ) ^ 2 ≤ B)
    (hscale : (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    R.tension < (1 / 4) * Real.log 3 := by
  have hmul : (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2)
      ≤ (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B := mul_le_mul_of_nonneg_left hB (sq_nonneg _)
  have hge := R.cos_avg_ge_circ
  have hc_gt : (3 : ℝ) ^ (-(1 : ℝ) / 4) < ∑ d, R.p d * Real.cos (R.θ d) := by linarith
  exact neg_log_lt_floor hc_gt

#print axioms Read.cos_theta_circ
#print axioms Read.tension_lt_floor_of_circ_moment


/-- The tension is at most `−log(1 − (2π/(N+1))²·B/2)` when the CIRCLE moment is bounded by `B`. -/
theorem Read.tension_le_of_circ_moment {N : ℕ} (R : Read N) {B : ℝ}
    (hB : ∑ d, R.p d * (circLag d : ℝ) ^ 2 ≤ B)
    (hlt : (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2 < 1) :
    R.tension ≤ - Real.log (1 - (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2) := by
  have hmul : (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2)
      ≤ (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B := mul_le_mul_of_nonneg_left hB (sq_nonneg _)
  have hge := R.cos_avg_ge_circ
  have hpos : (0 : ℝ) < 1 - (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2 := by linarith
  have hle : 1 - (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2
      ≤ ∑ d, R.p d * Real.cos (R.θ d) := by linarith
  have := Real.log_le_log hpos hle
  show - Real.log (∑ d, R.p d * Real.cos (R.θ d)) ≤ _
  linarith

/-- **THE TENSION VANISHES AS THE WINDOW OPENS**, from a bounded CIRCLE moment.

The hypothesis is the one a gapped theory can meet: a correlation with a finite correlation length
has a bounded second moment about the circle distance, at every extent. Bounding the RAW lag moment
instead asks for something no periodic correlation satisfies. -/
theorem tension_tendsto_zero_of_bounded_circ_moment (B : ℝ) (R : (N : ℕ) → Read N)
    (hmom : ∀ N, ∑ d, (R N).p d * (circLag d : ℝ) ^ 2 ≤ B) :
    Filter.Tendsto (fun N => (R N).tension) Filter.atTop (nhds 0) := by
  have hfac := aperture_factor_tendsto_zero B
  have hupper : Filter.Tendsto
      (fun N : ℕ => - Real.log (1 - (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2))
      Filter.atTop (nhds 0) := by
    have hc : Filter.Tendsto
        (fun N : ℕ => 1 - (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2) Filter.atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hfac
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hc
    simpa using this.neg
  refine squeeze_zero' (Filter.Eventually.of_forall (fun N => (R N).tension_nonneg)) ?_ hupper
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2 < 1 :=
    hfac.eventually_lt_const (by norm_num)
  filter_upwards [hev] with N hN
  exact (R N).tension_le_of_circ_moment (hmom N) hN

#print axioms tension_tendsto_zero_of_bounded_circ_moment

end MassGap.Moment
