# Clay — declarations behind the route

Companion to [CLAY-CHECKLIST.md](CLAY-CHECKLIST.md). The previous pair is in [archive/](archive/).

## 1. The lattice gap

`ClayCapstone.clay_gap_of_absolute_decay` takes transfer data `D`, the vacuum complement `V`, a
nonempty Rayleigh set, `PositiveTransfer D`, a rate `0 < ρ < 1`, and

    ∀ y ∈ V, ∃ K, ∀ n,  ‖(D.Tq ^ n) y‖ ≤ K · ρⁿ

and returns `opT D` self-adjoint, `spectrum ⊆ {1} ∪ [0, e^(log ρ)]`, `1` the top.

It is built from:

* `SecondEigenvalue.norm_le_of_absolute_iterate_bound` — at a fixed `y ≠ 0`, absolute decay is the
  ratio form at `C = K/‖y‖`, and `SecondEigenvalue.norm_le_of_iterate_bound` washes the constant out
  by dyadic descent to `‖Tq y‖ ≤ ρ‖y‖`;
* `SecondEigenvalue.lambdaTwo_le_of_absolute_iterate_bound` — every vector at once, into `lambdaTwo`;
* `ClayCapstone.bddAbove_rayleighSet_Tq` — boundedness, unconditional;
* `ClayCapstone.clay_gap_of_lambdaTwo` — the spectral conclusion.

## 2. The form is a state pairing

`GaugeInvariantAlgebra.gaugeInv_form_pow`: on the gauge-invariant transfer data,
`form x (Tⁿ x) = ν(θ_{2p} x · shiftⁿ x)`. `TransferGap.form_pow_diag` and
`ClayCapstone.norm_Tq_pow_mk_mul` convert that into `‖Tqⁿ [x]‖`. So L3's pairing bound is the
hypothesis of §1.

`HalfSpaceAlgebra.halfSpaceAlg` is built from observables local on finite link sets, so every vector
of the GNS space is the class of a local observable.

## 3. The links

**L1 — the state.** `ClayCapstone.exists_dlr_limit_of_free_family` gives a DLR limit at every
coupling. `DLRLimit.unique_dlr_of_local_kernel_near_const` turns a boundary-decay estimate on local
observables into uniqueness, and `ClayCapstone.tendsto_free_family_of_unique_dlr` turns uniqueness into
`atTop` convergence. `ReflectionHalfSpace.wilson_positiveTransfer_of_mixCube_limit` then supplies
reflection invariance, reflection positivity, shift invariance and `PositiveTransfer`, and
`ClayCapstone.wilsonGaugeInvMixCubeData` is the gauge-invariant data at that state.
`WilsonDLR.local_kernel_near_const_at_zero` is the estimate at coupling zero.

**L2 — the cluster bound.** `StrongCoupling.wilsonCorrConnObs_eq_bridging_sumObs` is the exact
expansion of a connected correlation of general observables. For plaquette products the resummation
is done: `StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow`,
`StrongCoupling.wilsonCorrConnF_abs_le_coreConstF_mul_rate_pow`, with rate `coreRate K β` and constant
`coreConst K β`, uniform in the volume through the touch degree `K = 64`.

**L3 — box to state.** `GaugeInvariantAlgebra.stateFree_pairing_shift_abs_le` and
`GaugeInvariantAlgebra.stateFree_pairing_shiftObs_abs_le` bound the reflected-shifted pairing in the
box state; `ReflectionHalfSpace.stateFree_symCube_reflection_invariant` gives the box reflection
invariance they take; `GaugeInvariantAlgebra.nu_pairing_abs_le_of_eventually` carries a bound eventually
uniform in the box to `ν`.

**L5 — a vector in the complement.** One gauge-invariant observable with
`ν(θ_{2p} x' · x') > 0` after mean subtraction, which makes the Rayleigh set nonempty.

## 4. The continuum step

`ScreenedGap.physical_gap_of_tension_at_screen`: a family of lattices at fixed physical screen
`L = (2kᵢ+2)·spacingᵢ`, each with a transfer-mode correlation `ρᵢ(d) = λᵢ^circLag d` and its read below
the floor, has physical mass `(−log λᵢ)/spacingᵢ ≥ κ*/L` at every member.

* `ZeroMode.rate_gt_of_tension` — the read below the floor bounds `(k+1)·(−log λ)` below;
* `ZeroMode.gap_phys_of_fixed_screen` — at a fixed screen the spacing cancels;
* `ZeroMode.correlation_gap_of_tension` and `WilsonBridge.wilson_correlation_gap` — the multi-mode form,
  a geometric envelope on the mode sum itself;
* `ZeroMode.substrate_ge_of_mode_share` — each mode's weight against the second moment.

The floor is `exp(−κ₀YM)`, `κ₀YM = ¼·log 3`, from
`VortexCount.kappa0_is_the_surface_entropy_density`.

## 5. Reconstruction and non-triviality

`WilsonOS.wilson_reconstructed_nontrivial` — Osterwalder–Schrader data from the Wilson reflected form,
through `WightmanData.os_reconstruction_wightman`.

`SpecVarianceFloor.spec_variance_floor` — `exp(−(|β|·card(boundaryPlaqs {l₀})·2)) · Var_μ(h)` bounds
the kernel's variance at every region containing `l₀`. `SpecVarianceFloor.wilson_eventual_variance_floor`
is its eventual form at `SU N`, `2 ≤ N`, and `VarianceBridge.clay_nontriviality_of_eventual_variance_floor`
turns it into a DLR state that is not a point mass.

## 6. Verification

```
python research/code/lean_build.py build MassGap
python research/code/certify/lean_axiom_footprints.py scan
python research/code/certify/lean_derived_literals.py scan
python research/code/certify/doc_cites_live_declarations.py scan
python -m pytest research/code/tests -q
```
