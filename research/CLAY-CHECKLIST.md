# Clay — the route

[CLAY-DETAIL.md](CLAY-DETAIL.md) carries the declarations. The previous pair is in
[archive/](archive/).

## The goal — the Clay Millennium Problem

> **Yang–Mills Existence and Mass Gap.** Prove that for any compact simple gauge group `G`, a
> non-trivial quantum Yang–Mills theory exists on `ℝ⁴` and has a mass gap `Δ > 0`. Existence includes
> establishing axiomatic properties at least as strong as those cited in Streater–Wightman and
> Osterwalder–Schrader.
>
> — A. Jaffe and E. Witten, *Quantum Yang–Mills Theory*, the Clay Mathematics Institute's official
> problem description.

The statement asks for all of the following, together, for every compact simple `G`:

| # | requirement | meaning |
| --- | --- | --- |
| **E** | **existence** | a quantum field theory on `ℝ⁴` satisfying the Wightman axioms (equivalently the Osterwalder–Schrader axioms for its Euclidean Schwinger functions): a Hilbert space with a unitary representation of the Poincaré group, a unique vacuum, local field operators, positivity of the energy |
| **Y** | **it is Yang–Mills** | the continuum limit of the Yang–Mills theory with gauge group `G`: its local fields correspond to gauge-invariant polynomials in the curvature, with the short-distance behaviour asymptotic freedom prescribes |
| **N** | **non-trivial** | not a free field: the interaction is present in the limit |
| **M** | **mass gap** | the Hamiltonian `H` has spectrum `{0} ∪ [Δ, ∞)` with `Δ > 0`: every state orthogonal to the vacuum carries energy at least `Δ` |

## How the lattice meets it

On a reflection-positive lattice the Hamiltonian is `−log T`, `T` the transfer operator, so **M** on
the lattice is: **`T` has spectrum in `{1} ∪ [0, ρ]` with `ρ < 1`, in infinite volume**, `Δ = −log ρ`.
**E** is Osterwalder–Schrader reconstruction from the lattice Schwinger functions, **Y** is the limit
of vanishing lattice spacing with the gap held in physical units, and **N** is a non-degenerate
infinite-volume state.

## How we get there

**1. M on the lattice — the transfer gap on ℤ⁴ from cluster decay.**

    ClayCapstone.clay_gap_of_absolute_decay
      per-vector decay  ‖Tqⁿ y‖ ≤ K_y · ρⁿ  on the vacuum complement
        →  opT self-adjoint,  spectrum ⊆ {1} ∪ [0, ρ],  1 the top

The constant is chosen per vector, so an absolute cluster estimate feeds it directly.
`GaugeInvariantAlgebra.gaugeInv_form_pow` writes `form x (Tⁿ x)` as the reflected-shifted pairing
`ν(θ x · shiftⁿ x)` in the infinite-volume state, so the decay to supply is of that pairing.

| link | content | tree |
| --- | --- | --- |
| L1 | the infinite-volume state `ν` as the `atTop` limit of the box states | `ClayCapstone.tendsto_free_family_of_unique_dlr` |
| L2 | a cluster bound for general local observables | `StrongCoupling.wilsonCorrConnObs_eq_bridging_sumObs`; plaquette case `StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow` |
| L3 | the box bound carried to `ν` | `GaugeInvariantAlgebra.stateFree_pairing_shift_abs_le`, `GaugeInvariantAlgebra.nu_pairing_abs_le_of_eventually` |
| L4 | per-vector decay → spectrum | **built**: `ClayCapstone.clay_gap_of_absolute_decay` |
| L5 | a nonzero vacuum-orthogonal vector | one positivity at one gauge-invariant observable |

The cluster expansion supplies L2 on `coreRate 64 β < 1`, the strong-coupling region.

**2. Y and M in the continuum — the gap in physical units from the entropy floor.**

    ScreenedGap.physical_gap_of_tension_at_screen
      lattices at a fixed physical screen L,  a transfer-mode correlation,  the read below the floor
        →  κ*/L ≤ (−log λ) / spacing   at every spacing,   κ* = −2·log(12·(1 − 3^(−1/4))/8) ≈ 2.04

This is the entroptic step. `ZeroMode.rate_gt_of_tension` turns the read below the floor into a
lower bound on mass × extent, and `ZeroMode.gap_phys_of_fixed_screen` cancels the spacing at a fixed
screen, leaving a physical mass bounded below uniformly as the spacing goes to zero. The transfer
operator of step 1 supplies the spectral form it takes.

**3. E and N — reconstruction and non-triviality.**

    WilsonOS.wilson_reconstructed_nontrivial        Osterwalder–Schrader → Wightman
    SpecVarianceFloor.wilson_eventual_variance_floor  a variance floor, uniform in the volume

## What we have

* **The gap capstone**: `ClayCapstone.clay_gap_of_absolute_decay`, axiom-clean.
* **The transfer data on ℤ⁴**: reflection positivity and `PositiveTransfer`, with the form identified
  as a state pairing by `GaugeInvariantAlgebra.gaugeInv_form_pow`.
* **Strong-coupling cluster bounds**, uniform in the volume, on the torus and on the ℤ⁴ box.
* **The entroptic continuum step**: `ZeroMode` and `ScreenedGap`, axiom-clean.
* **Non-triviality**: `SpecVarianceFloor.wilson_eventual_variance_floor`, axiom-clean.
* **Reconstruction**: `WilsonOS.wilson_reconstructed_nontrivial`, through
  `WightmanData.os_reconstruction_wightman`.

## Next

L2, L3 and L1 in that order: the general-observable cluster bound, its transport to `ν`, and the
state itself. Then the spectral form of step 2 from the transfer operator of step 1.

## How to check

```
python research/code/lean_build.py build MassGap
python research/code/certify/lean_axiom_footprints.py scan
python research/code/certify/lean_derived_literals.py scan
python research/code/certify/doc_cites_live_declarations.py scan
python -m pytest research/code/tests -q
```
