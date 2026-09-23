import Mathlib
import MassGap.Floor
import MassGap.Capacity
import MassGap.CubeArea

/-!
# MassGap.VortexCount — the counted weight `3^k * exp (-μ (4k+6))` and the bound it yields

`floorTerm μ k = (3 : ℝ) ^ k * exp (-μ * (4 * k + 6))` pairs two facts about the same object, a
directed cube path `s : Fin k → Fin 3`. `Floor.directed_surface_count` says there are `3 ^ k` such
paths; `CubeArea.boundary_card_eq` says the boundary of the cube configuration each one bounds has
exactly `4 * k + 6` faces. `floor_count_injection` and `floorTerm_exponent_is_the_area` state those
two ties in this file's own terms.

`log_floorTerm` gives `log (floorTerm μ k) = k log 3 - μ (4k + 6)`, and `floor_ratio_tendsto` gives
`k log 3 / (4k + 6) - μ → (1/4) log 3 - μ`. `kappa0_is_the_surface_entropy_density` restates that
limit with the denominator written as the boundary cardinality of an arbitrary family of paths, so
the ratio does not depend on which path is taken at each `k`.

`junction_of_floor_count` takes `floorTerm μ k ≤ Z k` at every `k` together with
`log (Z k) / (4k + 6) ≤ c` for `k > 0`, and concludes `(1/4) log 3 - μ ≤ c` by passing to the limit.
`floorTerm_le_weighted` discharges the first hypothesis from `3 ^ k ≤ M k`, and
`junction_of_physical_count`, `selfSourcingJunction_of_physical_count` and
`junction_of_entropy_density` are that composition in three hypothesis shapes.
`three_pow_le_card_of_embeds` and `three_pow_le_card_of_directed_surfaces` supply `3 ^ k ≤ M k` from
an injection of the directed paths into a `Finset`, with injectivity discharged by
`CubeArea.boundaryFaces_cubeConfig_injective`. `directed_surfaces_all_have_area` records that every
member of such a family has `4 * k + 6` faces.

`existence_and_gap_of_floor_count` feeds the junction to `Capacity.existence_and_gap_of_junction`,
and `floor_count_gap_demo` instantiates every hypothesis at `M k = 3 ^ k`, `μ ≡ 0`,
`c = Δ ≡ (1/4) log 3`.

Scope: `CubeArea.Face` is `Fin 3 × (Fin 3 → ℕ)`, a face of a three-dimensional sublattice, so the
family `V` in the containment statements is a family of three-dimensional surfaces; no embedding into
four-dimensional plaquettes is constructed here. The scale-duality hypotheses `hdual` and `hdens` are
supplied by the caller in every theorem that uses them. Axiom footprints are printed at the end of
the file.
-/

namespace MassGap.VortexCount

open Filter Topology

/-- The counted weight at `k` steps: `(3 : ℝ) ^ k * Real.exp (-μ * (4 * k + 6))`. The first factor is
the number of directed cube paths `Fin k → Fin 3`, which `Floor.directed_surface_count` computes; the
second is `exp (-μ * A)` at `A` the common boundary area of the surfaces those paths bound, which
`CubeArea.boundary_card_eq` computes. `floor_count_injection` and `floorTerm_exponent_is_the_area`
state those two identifications.

Scope: `μ` is an arbitrary real, of either sign; `floorTerm μ k` is strictly positive at every `μ`
and `k`.

DERIVED: `3` is the branching factor of a directed cube path, the cardinality of `Fin 3` at each of
the `k` steps. `4` and `6` are the boundary area `4 * k + 6`, equal to `4 * (k + 1) + 2`: six faces
per cube over `k + 1` cubes, less two per shared face over the `k` shared ones. -/
noncomputable def floorTerm (μ : ℝ) (k : ℕ) : ℝ := (3 : ℝ) ^ k * Real.exp (-μ * (4 * (k : ℝ) + 6))

/-- For every directed cube path `s : Fin k → Fin 3`,
`(CubeArea.boundaryFaces (cubeConfig s)).card = 4 * k + 6` as a real. It is
`CubeArea.boundary_card_eq` cast to `ℝ`, which is the form `floorTerm`'s exponent is written in.

Scope: the equality holds for EVERY `s` — the area does not depend on which path is taken — which is
what makes a single exponent correct for the whole family of `3 ^ k` surfaces.

DERIVED: `3` is the branching factor, the cardinality of `Fin 3` at each step; `4` and `6` are the
boundary area `4 * k + 6`, from `CubeArea.boundary_card_eq`. -/
theorem floorTerm_exponent_is_the_area {k : ℕ} (s : Fin k → Fin 3) :
    ((MassGap.CubeArea.boundaryFaces (MassGap.cubeConfig s)).card : ℝ) = 4 * (k : ℝ) + 6 := by
  rw [MassGap.CubeArea.boundary_card_eq s]
  push_cast
  ring

/-- `floorTerm μ k = (Finset.univ.image (@cubeConfig k)).card * Real.exp (-μ * (4 * k + 6))`: the
first factor of `floorTerm` is the cardinality of the image of `cubeConfig`, by
`MassGap.directed_surface_count`. So a weight dominating the counted family's weight dominates
`floorTerm`.

Scope: an identity, holding at every real `μ` and every `k`.

DERIVED: `4` and `6` are the boundary area `4 * k + 6`, carried over from `floorTerm`. The `3` is
not written here — it has been replaced by the cardinality expression this theorem equates it to. -/
theorem floor_count_injection (μ : ℝ) (k : ℕ) :
    floorTerm μ k
      = ((Finset.univ.image (@MassGap.cubeConfig k)).card : ℝ) * Real.exp (-μ * (4 * (k : ℝ) + 6)) := by
  unfold floorTerm
  rw [MassGap.directed_surface_count]
  push_cast
  ring

/-- `Real.log (floorTerm μ k) = k * Real.log 3 - μ * (4 * k + 6)`. Both factors of `floorTerm` are
nonzero — a power of `3` and an exponential — so `Real.log_mul` applies, and `Real.log_pow` and
`Real.log_exp` evaluate the two pieces.

DERIVED: `3` is the base of the counted factor, whose logarithm appears; `4` and `6` are the
boundary area `4 * k + 6`, carried over from `floorTerm`. -/
theorem log_floorTerm {μ : ℝ} (k : ℕ) :
    Real.log (floorTerm μ k) = (k : ℝ) * Real.log 3 - μ * (4 * (k : ℝ) + 6) := by
  unfold floorTerm
  rw [Real.log_mul (pow_ne_zero k (by norm_num : (3 : ℝ) ≠ 0)) (Real.exp_ne_zero _),
      Real.log_pow, Real.log_exp]
  ring

/-- `fun k : ℕ => k * Real.log 3 / (4 * k + 6) - μ` tends to `1 / 4 * Real.log 3 - μ` along
`Filter.atTop`. The proof rewrites `k / (4k + 6)` as `1 / (4 + 6/k)` eventually, sends `6/k → 0`, and
multiplies the resulting limit `1/4` by `Real.log 3` before subtracting the constant `μ`.

Scope: the limit is over the natural-number index `k`; `μ` is a constant real subtracted throughout.

DERIVED: `3` is the base of the logarithm, the branching factor of a directed cube path, appearing in
both the sequence and the limit; `4` and `6` are the boundary area `4 * k + 6` in the denominator;
`1` and the second `4` are the limit `1 / 4` of `k / (4 * k + 6)`, the reciprocal area per step. -/
theorem floor_ratio_tendsto {μ : ℝ} :
    Tendsto (fun k : ℕ => (k : ℝ) * Real.log 3 / (4 * (k : ℝ) + 6) - μ) atTop
      (𝓝 (1 / 4 * Real.log 3 - μ)) := by
  have hnd : Tendsto (fun k : ℕ => (k : ℝ) / (4 * (k : ℝ) + 6)) atTop (𝓝 (1 / 4)) := by
    have he : (fun k : ℕ => (k : ℝ) / (4 * (k : ℝ) + 6)) =ᶠ[atTop]
        (fun k : ℕ => 1 / (4 + 6 / (k : ℝ))) := by
      filter_upwards [eventually_gt_atTop 0] with k hk
      have hne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
      field_simp
    rw [tendsto_congr' he]
    have h6 : Tendsto (fun k : ℕ => (6 : ℝ) / (k : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 6
    have hden : Tendsto (fun k : ℕ => (4 : ℝ) + 6 / (k : ℝ)) atTop (𝓝 4) := by
      simpa using (tendsto_const_nhds (x := (4 : ℝ))).add h6
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have := hc.div hden (by norm_num)
    simpa [Pi.div_def, one_div] using this
  have hmain : Tendsto (fun k : ℕ => (k : ℝ) * Real.log 3 / (4 * (k : ℝ) + 6)) atTop
      (𝓝 (1 / 4 * Real.log 3)) := by
    have := hnd.mul_const (Real.log 3)
    have he : (fun k : ℕ => (k : ℝ) / (4 * (k : ℝ) + 6) * Real.log 3)
        = (fun k : ℕ => (k : ℝ) * Real.log 3 / (4 * (k : ℝ) + 6)) := by
      funext k; ring
    rw [he] at this
    simpa using this
  simpa using hmain.sub_const μ

/-- For any family of directed cube paths `s : ∀ k : ℕ, Fin k → Fin 3`,

    Real.log (3 ^ k) / (CubeArea.boundaryFaces (cubeConfig (s k))).card  →  1 / 4 * Real.log 3

along `Filter.atTop`. The numerator is `Real.log_pow`, giving `k * log 3`; the denominator is
`CubeArea.boundary_card_eq`, giving `4 * k + 6`; the limit is `floor_ratio_tendsto` at `μ = 0`.

Scope: the family `s` is arbitrary and unused beyond typing — the ratio is the same whichever path
is taken at each `k`, because every one of them bounds a surface of the same area. The numerator is
the logarithm of the count `3 ^ k` rather than of a cardinality expression.

DERIVED: the first `3` is the branching factor, the cardinality of `Fin 3` at each step; the second
`3` is the base of the counted family `3 ^ k`; `1` and `4` are the limiting reciprocal area per
step, and the final `3` is the base of the logarithm in the limit. -/
theorem kappa0_is_the_surface_entropy_density (s : ∀ k : ℕ, Fin k → Fin 3) :
    Tendsto (fun k : ℕ => Real.log ((3 : ℝ) ^ k)
        / ((MassGap.CubeArea.boundaryFaces (MassGap.cubeConfig (s k))).card : ℝ))
      atTop (𝓝 (1 / 4 * Real.log 3)) := by
  have he : (fun k : ℕ => Real.log ((3 : ℝ) ^ k)
        / ((MassGap.CubeArea.boundaryFaces (MassGap.cubeConfig (s k))).card : ℝ))
      = (fun k : ℕ => (k : ℝ) * Real.log 3 / (4 * (k : ℝ) + 6)) := by
    funext k
    rw [Real.log_pow, MassGap.CubeArea.boundary_card_eq (s k)]
    push_cast
    ring_nf
  rw [he]
  simpa using floor_ratio_tendsto (μ := 0)

#print axioms kappa0_is_the_surface_entropy_density

/-- Given `floorTerm μ k ≤ Z k` at every `k`, and `Real.log (Z k) / (4 * k + 6) ≤ c` at every `k > 0`,
it follows that `1 / 4 * Real.log 3 - μ ≤ c`.

The proof takes the limit of `floor_ratio_tendsto` against the eventual bound: at `k > 0`,
`log (floorTerm μ k) ≤ log (Z k)` by monotonicity of the logarithm (`floorTerm μ k` is strictly
positive), `log_floorTerm` expands the left side, and dividing by the positive `4 * k + 6` gives
`k log 3 / (4k+6) - μ ≤ log (Z k) / (4k+6) ≤ c`.

Scope: `Z` need not be positive or monotone; only the domination `floorTerm μ k ≤ Z k` is used, and
it forces `Z k > 0`. `hdual` is required only at `k > 0`, which is all the `atTop` filter needs.

DERIVED: `0` is the lower bound on `k` in `hdual`, excluding the degenerate index; `4` and `6` are
the boundary area `4 * k + 6` in the denominator; `1` and the second `4` are the limiting reciprocal
area per step; `3` is the base of the logarithm, the branching factor. -/
theorem junction_of_floor_count {μ c : ℝ} {Z : ℕ → ℝ}
    (hZ : ∀ k, floorTerm μ k ≤ Z k)
    (hdual : ∀ k, 0 < k → Real.log (Z k) / (4 * (k : ℝ) + 6) ≤ c) :
    1 / 4 * Real.log 3 - μ ≤ c := by
  refine le_of_tendsto floor_ratio_tendsto ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hpos : 0 < floorTerm μ k := by unfold floorTerm; positivity
  have hlog : (k : ℝ) * Real.log 3 - μ * (4 * (k : ℝ) + 6) ≤ Real.log (Z k) := by
    calc (k : ℝ) * Real.log 3 - μ * (4 * (k : ℝ) + 6)
        = Real.log (floorTerm μ k) := (log_floorTerm k).symm
      _ ≤ Real.log (Z k) := Real.log_le_log hpos (hZ k)
  have h6 : 0 < (4 * (k : ℝ) + 6) := by positivity
  have hdiv : (k : ℝ) * Real.log 3 / (4 * (k : ℝ) + 6) - μ ≤ Real.log (Z k) / (4 * (k : ℝ) + 6) := by
    have hstep := (div_le_div_iff_of_pos_right h6).mpr hlog
    have hrw : ((k : ℝ) * Real.log 3 - μ * (4 * (k : ℝ) + 6)) / (4 * (k : ℝ) + 6)
        = (k : ℝ) * Real.log 3 / (4 * (k : ℝ) + 6) - μ := by field_simp
    rwa [hrw] at hstep
  exact le_trans hdiv (hdual k hk)

/-! ### Supplying `hZ` from a cardinality bound `3 ^ k ≤ M k` -/

/-- If `3 ^ k ≤ M k` at every `k`, then `floorTerm μ k ≤ M k * Real.exp (-μ * (4 * k + 6))`. The
exponential factor is common to both sides and nonnegative, so the inequality reduces to the cast of
`hM`.

Scope: `M : ℕ → ℕ`, so the bound is on a natural-number count; `μ` may have either sign, since only
nonnegativity of the exponential is used.

DERIVED: `3` is the branching factor of a directed cube path, the count `floorTerm` carries; `4` and
`6` are the boundary area `4 * k + 6` in the shared exponential. -/
theorem floorTerm_le_weighted {μ : ℝ} {M : ℕ → ℕ} (hM : ∀ k, 3 ^ k ≤ M k) (k : ℕ) :
    floorTerm μ k ≤ (M k : ℝ) * Real.exp (-μ * (4 * (k : ℝ) + 6)) := by
  unfold floorTerm
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
  exact_mod_cast hM k

/-- If `ι : (Fin k → Fin 3) → S` is injective and lands in a `Finset S` called `V`, then
`3 ^ k ≤ V.card`. The image of `Finset.univ` under `ι` is a subset of `V` with cardinality
`Fintype.card (Fin k → Fin 3) = 3 ^ k`, by `Finset.card_image_of_injective` and
`MassGap.directed_paths_card`.

Scope: `S` is an arbitrary type with decidable equality; nothing ties it to surfaces, faces or a
lattice. Both injectivity and the containment are hypotheses.

DERIVED: the first `3` is the cardinality of `Fin 3`, the branching at each step of the domain
`Fin k → Fin 3`; the second `3` is the resulting count `3 ^ k`. -/
theorem three_pow_le_card_of_embeds {k : ℕ} {S : Type} [DecidableEq S]
    (V : Finset S) (ι : (Fin k → Fin 3) → S) (hι : Function.Injective ι)
    (hsub : ∀ p, ι p ∈ V) : 3 ^ k ≤ V.card := by
  have himg : Finset.univ.image ι ⊆ V := by
    intro s hs
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hs
    exact hsub p
  calc 3 ^ k = (Finset.univ.image ι).card := by
        rw [Finset.card_image_of_injective _ hι, Finset.card_univ, MassGap.directed_paths_card]
    _ ≤ V.card := Finset.card_le_card himg

/-- `three_pow_le_card_of_embeds` at the map `CubeArea.boundaryFaces ∘ cubeConfig`: if every directed
cube path's boundary surface belongs to a `Finset (Finset CubeArea.Face)` called `V`, then
`3 ^ k ≤ V.card`. Injectivity of the map is discharged internally by
`CubeArea.boundaryFaces_cubeConfig_injective`, which recovers each cube from the boundary through the
face its step crosses, so the only hypothesis left to the caller is the containment `hsub`.

Scope: `V` is a family of SURFACES — sets of faces — not of cube positions.
`CubeArea.Face` is `Fin 3 × (Fin 3 → ℕ)`, a face of a three-dimensional sublattice, so `hsub` is a
statement about three-dimensional surfaces; no embedding into four-dimensional plaquettes appears
here.

DERIVED: the first `3` is the cardinality of `Fin 3`, the branching at each step of the directed
path `s : Fin k → Fin 3`; the second `3` is the resulting count `3 ^ k`. -/
theorem three_pow_le_card_of_directed_surfaces {k : ℕ}
    (V : Finset (Finset MassGap.CubeArea.Face))
    (hsub : ∀ s : Fin k → Fin 3,
      MassGap.CubeArea.boundaryFaces (MassGap.cubeConfig s) ∈ V) :
    3 ^ k ≤ V.card :=
  three_pow_le_card_of_embeds V _ MassGap.CubeArea.boundaryFaces_cubeConfig_injective hsub

#print axioms three_pow_le_card_of_directed_surfaces

/-- If every member of `V : Finset (Finset CubeArea.Face)` is the boundary surface of some directed
cube path `s : Fin k → Fin 3`, then every member has cardinality `4 * k + 6`. The proof destructures
the hypothesis and applies `CubeArea.boundary_card_eq`.

This is what makes a single exponent `exp (-μ * (4 * k + 6))` correct for the whole family rather
than a mixture over different areas.

Scope: the hypothesis is that every member of `V` arises from some path — the converse containment of
`three_pow_le_card_of_directed_surfaces`'s `hsub`. The two together say `V` is exactly the family of
directed boundaries.

DERIVED: `3` is the branching factor, the cardinality of `Fin 3` at each step; `4` and `6` are the
boundary area `4 * k + 6`. -/
theorem directed_surfaces_all_have_area {k : ℕ}
    (V : Finset (Finset MassGap.CubeArea.Face))
    (hV : ∀ F ∈ V, ∃ s : Fin k → Fin 3, F = MassGap.CubeArea.boundaryFaces (MassGap.cubeConfig s)) :
    ∀ F ∈ V, F.card = 4 * k + 6 := by
  intro F hF
  obtain ⟨s, rfl⟩ := hV F hF
  exact MassGap.CubeArea.boundary_card_eq s

#print axioms directed_surfaces_all_have_area

/-- `junction_of_floor_count` with the domination hypothesis replaced by the cardinality bound
`3 ^ k ≤ M k`: given that, and
`Real.log (M k * Real.exp (-μ * (4 * k + 6))) / (4 * k + 6) ≤ c` at every `k > 0`, it follows that
`1 / 4 * Real.log 3 - μ ≤ c`. The first hypothesis is converted by `floorTerm_le_weighted`.

Scope: `hdual` is a hypothesis on the caller — it bounds the weighted count's logarithmic density by
`c` and is not derived anywhere in this file.

DERIVED: `3` is the branching factor in `3 ^ k ≤ M k`, and appears again as the base of the
logarithm in the conclusion; `0` is the lower bound on `k` in `hdual`; `4` and `6` appear twice, as
the boundary area `4 * k + 6` inside the exponential and again as the denominator; `1` and the final
`4` are the limiting reciprocal area per step. -/
theorem junction_of_physical_count {μ c : ℝ} {M : ℕ → ℕ}
    (hM : ∀ k, 3 ^ k ≤ M k)
    (hdual : ∀ k, 0 < k →
      Real.log ((M k : ℝ) * Real.exp (-μ * (4 * (k : ℝ) + 6))) / (4 * (k : ℝ) + 6) ≤ c) :
    1 / 4 * Real.log 3 - μ ≤ c :=
  junction_of_floor_count (fun k => floorTerm_le_weighted hM k) hdual

/-- `junction_of_physical_count` restated as `Capacity.SelfSourcingJunction (1 / 4 * Real.log 3) μ c`.
That structure unfolds to the same inequality, so the proof is the previous theorem unchanged; the
difference is the form in which the conclusion is offered to `Capacity`'s consumers.

Scope: the first argument of `SelfSourcingJunction` is fixed at `1 / 4 * Real.log 3`; this does not
state the junction at any other value.

DERIVED: `3` is the branching factor in `3 ^ k ≤ M k`, and again the base of the logarithm in the
conclusion; `0` is the lower bound on `k` in `hdual`; `4` and `6` appear twice, as the boundary area
`4 * k + 6` inside the exponential and again as the denominator; `1` and the final `4` are the
limiting reciprocal area per step. -/
theorem selfSourcingJunction_of_physical_count {μ c : ℝ} {M : ℕ → ℕ}
    (hM : ∀ k, 3 ^ k ≤ M k)
    (hdual : ∀ k, 0 < k →
      Real.log ((M k : ℝ) * Real.exp (-μ * (4 * (k : ℝ) + 6))) / (4 * (k : ℝ) + 6) ≤ c) :
    MassGap.Capacity.SelfSourcingJunction (1 / 4 * Real.log 3) μ c :=
  junction_of_physical_count hM hdual

/-- The same conclusion `1 / 4 * Real.log 3 - μ ≤ c` from the hypothesis in unweighted form:
`3 ^ k ≤ M k` at every `k`, and `Real.log (M k) / (4 * k + 6) ≤ μ + c` at every `k > 0`. The proof
splits `log (M k * exp (-μ (4k+6)))` with `Real.log_mul` — legitimate because `3 ^ k ≤ M k` makes
`M k` positive — evaluates the exponential's logarithm, and cancels the `-μ` term to reach
`junction_of_physical_count`'s hypothesis.

Scope: `hdens` is a hypothesis on the caller. It bounds the logarithmic density of the count itself,
with the tension `μ` moved to the right-hand side.

DERIVED: `3` is the branching factor in `3 ^ k ≤ M k`, and again the base of the logarithm in the
conclusion; `0` is the lower bound on `k` in `hdens`; `4` and `6` are the boundary area `4 * k + 6`
in the denominator; `1` and the final `4` are the limiting reciprocal area per step. -/
theorem junction_of_entropy_density {μ c : ℝ} {M : ℕ → ℕ}
    (hM : ∀ k, 3 ^ k ≤ M k)
    (hdens : ∀ k, 0 < k → Real.log (M k : ℝ) / (4 * (k : ℝ) + 6) ≤ μ + c) :
    1 / 4 * Real.log 3 - μ ≤ c := by
  refine junction_of_physical_count hM (fun k hk => ?_)
  have hMpos : (0 : ℝ) < (M k : ℝ) := by
    have : 0 < M k := lt_of_lt_of_le (pow_pos (by norm_num) k) (hM k)
    exact_mod_cast this
  have h6 : (0 : ℝ) < 4 * (k : ℝ) + 6 := by positivity
  rw [Real.log_mul (ne_of_gt hMpos) (Real.exp_ne_zero _), Real.log_exp, add_div,
    show (-μ * (4 * (k : ℝ) + 6)) / (4 * (k : ℝ) + 6) = -μ by field_simp]
  linarith [hdens k hk]

/-- `Capacity.existence_and_gap_of_junction` with its junction hypothesis supplied by
`selfSourcingJunction_of_physical_count`. Given, at every coupling `β`: a mode bound
`‖m β k‖ ≤ exp (-Δ β)` on the index set `s β`; the cardinality bound `3 ^ k ≤ M β k`; the
scale-duality `hdual`; `c β ≤ Δ β`; `μ β < 1 / 4 * Real.log 3`; and isotropy `R d = R d'` — the
conclusion conjoins three statements:

* `‖∑ k ∈ s β, P β k * (m β k) ^ τ‖ → 0` as `τ → atTop`, at every `β`;
* `μ β - 1 / 4 * Real.log 3 < 0` at every `β`, which is `hconf` rearranged;
* `R d = R d'` for all `d`, `d'`, which is `hiso` unchanged.

Scope: `Idx` and `Dir` are arbitrary types and `P`, `m`, `R`, `s` are arbitrary functions — nothing
here ties them to a lattice, a spectrum or a rotation group. Both `κ₀` arguments of
`existence_and_gap_of_junction` are instantiated at `1 / 4 * Real.log 3`, with `le_refl` supplying
their comparison. The second and third conjuncts are restatements of hypotheses.

DERIVED: `3` is the branching factor in `3 ^ k ≤ M β k`, and appears again as the base of the
logarithm in `hconf` and in the second conjunct; `0` is the lower bound on `k` in `hdual`, the limit
in the first conjunct, and the comparison point in the second; `4` and `6` appear twice, as the
boundary area `4 * k + 6` inside the exponential and again as the denominator; `1` and `4` appear
twice more, as the reciprocal area per step in `hconf` and in the second conjunct. -/
theorem existence_and_gap_of_floor_count {Idx Dir : Type}
    (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (R : Dir → ℝ)
    (μ Δ c : ℝ → ℝ) {M : ℝ → ℕ → ℕ}
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hM : ∀ β k, 3 ^ k ≤ M β k)
    (hdual : ∀ β k, 0 < k →
      Real.log ((M β k : ℝ) * Real.exp (-μ β * (4 * (k : ℝ) + 6))) / (4 * (k : ℝ) + 6) ≤ c β)
    (hgap : ∀ β, c β ≤ Δ β)
    (hconf : ∀ β, μ β < 1 / 4 * Real.log 3) (hiso : ∀ d d', R d = R d') :
    (∀ β, Filter.Tendsto (fun τ => ‖∑ k ∈ s β, P β k * (m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, μ β - 1 / 4 * Real.log 3 < 0) ∧ (∀ d d', R d = R d') :=
  MassGap.Capacity.existence_and_gap_of_junction s P m R (1 / 4 * Real.log 3) (1 / 4 * Real.log 3)
    μ Δ c (le_refl _) hdom
    (fun β => selfSourcingJunction_of_physical_count (hM β) (hdual β)) hgap hconf hiso

/-- An instance of `existence_and_gap_of_floor_count` with every parameter fixed, so the statement
has no hypotheses. The instantiation is: index and direction types `Unit`, index set
`Finset.univ : Finset Unit`, projections `P ≡ 1`, modes `m ≡ exp (-(1/4 * log 3))`, radii `R ≡ 0`,
tension `μ ≡ 0`, contraction and gap `c = Δ ≡ 1/4 * log 3`, and count `M k = 3 ^ k` — the tight case
of `hM`. The six side goals are discharged by `rfl`, `le_refl`, positivity of `log 3`, and one
`nlinarith` for the scale-duality at `μ = 0`.

The conclusion conjoins: the norm of the one-term sum tends to `0`; `0 - 1/4 * log 3 < 0`; and
`(0 : ℝ) = 0` for all pairs of `Unit`. It is a witness that the hypotheses of
`existence_and_gap_of_floor_count` are jointly satisfiable.

Scope: every quantity is constant in `β`, and the index set has one element, so the sum has one
term. The third conjunct is trivially true and carries no content beyond typing.

DERIVED: `1` occurs twice, as the projection coefficient `(1 : ℂ)` and as the numerator of
`1 / 4 * Real.log 3`; `4` occurs twice and `3` occurs twice, as the denominator and the logarithm's
base in each copy of `1 / 4 * Real.log 3`; `0` occurs five times — the limit of the norm, the
tension value `(0 : ℝ)`, the comparison point of the second conjunct, and the two sides of the
isotropy equation `(0 : ℝ) = 0`. -/
theorem floor_count_gap_demo :
    (∀ _β : ℝ, Filter.Tendsto (fun τ => ‖∑ _k ∈ (Finset.univ : Finset Unit),
        (1 : ℂ) * ((Real.exp (-(1 / 4 * Real.log 3)) : ℝ) : ℂ) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ _β : ℝ, (0 : ℝ) - 1 / 4 * Real.log 3 < 0) ∧
      (∀ _d _d' : Unit, (0 : ℝ) = 0) := by
  have hκ₀ : (0 : ℝ) < 1 / 4 * Real.log 3 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 3); linarith
  have hlog : (0 : ℝ) ≤ Real.log 3 := (Real.log_pos (by norm_num)).le
  refine existence_and_gap_of_floor_count
    (fun _ => (Finset.univ : Finset Unit)) (fun _ _ => (1 : ℂ))
    (fun _ _ => ((Real.exp (-(1 / 4 * Real.log 3)) : ℝ) : ℂ)) (fun _ => (0 : ℝ))
    (fun _ => (0 : ℝ)) (fun _ => 1 / 4 * Real.log 3) (fun _ => 1 / 4 * Real.log 3)
    (M := fun _ k => 3 ^ k) ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _
    refine le_of_eq ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  · intro _ _; exact le_refl _
  · intro _ k _
    simp only [neg_zero, zero_mul, Real.exp_zero, mul_one]
    push_cast
    rw [Real.log_pow, div_le_iff₀ (by positivity)]
    nlinarith [hlog, mul_nonneg hlog (Nat.cast_nonneg k)]
  · intro _; exact le_refl _
  · intro _; exact hκ₀
  · intro _ _; rfl

#print axioms floorTerm_exponent_is_the_area
#print axioms floor_count_injection
#print axioms junction_of_floor_count
#print axioms three_pow_le_card_of_embeds
#print axioms junction_of_physical_count
#print axioms selfSourcingJunction_of_physical_count
#print axioms existence_and_gap_of_floor_count
#print axioms floor_count_gap_demo

end MassGap.VortexCount
