# Box local gap: an upper read of `BoxPatch.BoxLocalGap`, SU(2)

Files: `box_gap_calib.py` (the read), `box_gap_calib_node45.sh` (the launcher for the compute node).
Nothing here has run beyond the self-test and toy runs of a few seconds on the workstation.

## What the Lean constant is

On the torus of extent `L = 2(j + 1)`, the box of side `n ≤ L/2` at corner `k` owns the `4n⁴` links
`(μ, x)` with `x − k ∈ [0, n)⁴`. That includes the links pointing out of the box on its `+` faces.
`boxOp β n j k = Σ_{l ∈ box} (I − E_l)`, where `E_l = torusCondExp` is the single-link heat bath,
acting on the periodic gauge-invariant observables with `torusForm`, the Gibbs L² form. Call it `A`.
`A` is self-adjoint and `0 ≤ A ≤ |B|`. Its kernel is the observables that read no box link. The
projection onto that kernel is `E_B`, the conditional expectation given the links outside the box.

`γ⟨Ax, x⟩ ≤ ⟨Ax, Ax⟩` for every `x` holds exactly when `γ ≤ λ₁(β, n, L)`, the least non-zero spectral
value of `A`. So:

    BoxPatchGap β n γ holds for some γ   ⇔   (40n − 36)/n² < inf_L λ₁(β, n, L)   (n ≥ 2).

`BoxFibreGap` (one box under every frozen boundary) implies `BoxLocalGap`, so refuting the local form
refutes the fibre form too.

**Coupling convention.** `Plaq` runs over ordered direction pairs, so the Lean action is twice the
standard Wilson action and `β_lean = β_std/2`. PAPER.md records this too. The script takes `β_std`,
which is the generator's convention, and writes both columns. John's crossover window `β_std ∈ [1.5, 3]`
is `β_lean ∈ [0.75, 1.5]`. `PairCorr.boxPatchGap_at` is at `β_lean = 1/241920`.

## The analytic ceiling (a lead, not yet a Lean theorem)

Take the plaquette `(0, 1)` based at `k − e₁`. It reads one box link, `(0, k)`, and three links
outside every box with corner `k`. For `y = x − E_B x`:

    ⟨Ay, y⟩/⟨y, y⟩ = E Var_l(x) / E Var_B(x) ≤ 1.

This is the law of total variance: `E_B` conditions on less than `E_l` does. So `λ₁ ≤ 1` at every `β`
and every `n`. Since `(40n − 36)/n² ≥ 1` for `n ≤ 39`, no box side below 40 can satisfy
`BoxPatchGap` at any coupling. `BoxGap.boxPatchGap_zero` (`γ = 1`, `n ≥ 40` at `β = 0`) is the
equality case. For `β > 0`, `E_l x` reads neighbouring box links, so the inequality is strict, and
`n = 40` needs `γ ∈ (0.9775, λ₁]`. The `corner` observable measures how far below 1 this ceiling sits.

## What the script measures

These are statistical upper bounds on `λ₁`, taken from equilibrium boundaries and the exact
random-scan box heat bath `P = I − A/|B|`:

| estimator | bound | where it is valid |
|---|---|---|
| `rq_fixed`, `rq_ritz` | Rayleigh: `λ₁ ≤ Σ_l E Var_l(x) / E Var_B(x)`. The numerator is closed form from the SU(2) heat-bath moments (`I₂/I₁`); the denominator is the fibre variance of the box chain. | At the measured box. Transferable observables also give a bound at every larger box with the same corner on the same torus. |
| `ac_fixed`, `ac_ritz` | Semigroup: `P ≥ 0` on `ker A^⊥`, so `ρ_K ≤ (1 − λ₁/|B|)^K`, which gives `λ₁ ≤ |B|(1 − ρ_K^{1/K})` after `K = s|B|` single-link updates. | At the measured box only. |

- **`ritz`** minimises the bound over a family of plaquette-sum observables, using a generalised
  eigenproblem. It is cross-fitted: the combination is chosen on half of the boundaries and evaluated
  on the other half, so the choice cannot pull the bound low.
- **Family `T` (transferable).** These observables read only box links and links on the negative
  side of the corner (`nunsafe = 0`). For them, `rq` at side `n₀` bounds every side `n ∈ [n₀, L/2]`:
  the numerator is unchanged, and `E Var_B` only grows with the box.
- **Family `F`** is every observable.
- **Observables:**
  - Class means of the plaquettes that touch the box, keyed by (box links, safe outside, unsafe
    outside) or by interior depth, each also weighted by the lowest box mode (`~s`).
  - One interior profile (`prof`).
  - The `corner` probe.
- **Controls that run in `--selftest`:**
  - The gathered staples equal the generator's `_su2_staple`: difference 0.
  - Each staple closes its plaquette: difference 3e-16.
  - The closed-form `Cov_l` agrees with 400k heat-bath draws at `β = 0, 0.7, 2.3` (within 1.2σ).
  - The layered schedule reproduces the sequential chain bit for bit. The negative control (no
    layering) differs by 1.3.
- **Known answer at `β = 0`.** A plaquette with `j` box links is an eigenvector of `A` with eigenvalue
  `j`. The toy run read `rq = 1.02, 2.07, 3.19, 4.00` for `j = 1, 2, 3, 4` and `1.06` for the corner.
  That run had 6 samples. The `pilot` repeats this control at full statistics.
- **The fibre mean is subtracted per box chain.** That bias pushes `rq` and `ac` up, which works
  against a refutation. It is about `2τ/T`. The toy's `ac` at `β = 0` reads 1.37 against the exact 1
  with `T = 24` sweeps. The defaults use `T = 200` (100 at `n = 3`).

## What it can refute, and what it cannot certify

- **Refutes.** Suppose a pre-registered primary row's upper 97.5% limit `ci_hi` sits below
  `(40n − 36)/n²`. Then `BoxPatchGap` is refuted at `(β, n)`, for every `γ`, at that torus
  (`refutes_at_n`). This holds up to the confidence level. The primary rows are `rq_ritz T` and
  `ac_ritz F` at `--primary-lag` (4 sweeps). Every other row is diagnostic, and taking a minimum
  across rows is a multiple comparison.
- **Lower-bounds the side.** `n_min_implied` is the least side that a gap of at most `ci_hi` allows.
  For `rq_ritz T` it holds for `n ≤ L/2` on the measured torus. The sides it names are 40 or more,
  which is beyond any `L` this can run. It carries to those sides only under the assumption that the
  read does not depend on `L`. The `L = 8, 12, 16` rows at `n = 2` test that assumption; they do not
  prove it.
- **Cannot certify.**
  - A lower bound on `λ₁` is an infimum over all observables. No finite family spans that space.
  - `BoxLocalGap` also asks for every torus.
  - `BoxFibreGap` asks for every boundary, and equilibrium sampling never reaches the worst one.
  - A read above the threshold is consistent with `BoxPatchGap` and is not evidence for it.
- **Why the transfer spectrum is not the read.** `(I − T)/a` is the physical gap: the program's
  conclusion, not this input. No inequality in the Lean chain turns a transfer gap into a heat-bath
  box gap, in either direction. At most it gives `ξ`, context for where `λ₁` might fall.

## Existing numerics reused

- `research/code/lattice_generator.py` is imported, not copied. Its path and sha256 are logged. The
  import uses:
  - the Kennedy–Pendleton/Creutz heat bath `_su2_heatbath_link`
  - `_su2_overrelax_link`, `_su2_staple`, `_su2_hb_sweep` (torus equilibrium) and `_su2_action`
  - the quaternion product
- `tests/test_generator_physics.py` already checks its plaquette against strong- and weak-coupling
  analytic values. The torus plaquette is a CSV row; run `--start cold` beside the default hot start
  as a thermalisation bracket.
- Gaugefields.jl is not needed. It would check equilibrium, and the new part here is the box dynamics,
  which the self-test checks.
- No existing script reads a heat-bath box gap. `certify/gap_of_box_operator.py` is the
  physical-volume transfer read, which is a different "box".

## Grid and runtime

Timings are from one workstation core. The pilot's `*.provenance.json` records the node's own
figures.

| piece | cost |
|---|---|
| torus compound sweep (HB + 4 OR), `L = 8` | 0.25 s (scales as `L⁴`) |
| box sweep incl. records and Rayleigh, `n = 2`, 16 boxes | 25 ms |
| same, `n = 3`, 16 boxes | 130 ms |
| same, `n = 4`, 1 box | 33 ms |
| per `(β, n = 2, L = 8)`: 200 boundaries × 200 sweeps | ≈ 20 min |
| per `(β, n = 3, L = 8)`: 60 × 100 | ≈ 15 min |
| per `(β, n = 4, L = 8)`: 200 × 200 | ≈ 25 min |
| per `(β, n = 2)` at `L = 12` / `L = 16` (16 boxes) | ≈ 31 / 63 min |

| tier | contents | CPU | wall (2 single-thread jobs) |
|---|---|---|---|
| `pilot` | self-test; `β = 0, 2.3`, `n = 2`, `L = 8`, 40 boundaries; `β = 2.3` cold start | ≈ 15 min | ≈ 15 min |
| `core` | `β_std ∈ {0, 1.5, 2.0, 2.3, 2.5, 3.0}`, `n = 2, 3, 4` at `L = 8`; `n = 2` at `L = 12, 16` for `β ∈ {2.0, 2.5}` | ≈ 9 h | ≈ 5 h |
| `full` | 11 couplings `0 … 3.0`; L-check at 5 | ≈ 19 h | ≈ 11 h |

SU(3) is not implemented. The Lean `E_l` is the exact SU(3) link heat bath, which Cabibbo–Marinari
only approximates. A faithful version would do one of two things:

- emulate `E_l` with many CM hits and show the read is stable in the hit count, or
- keep only the `ac` bound, because the closed-form Rayleigh numerator is SU(2)'s.

## The commands

Run these from the repository root in a POSIX shell. The host, port and key are read from the
git-ignored `research.local.env` (`COMPUTE_HOST`, `COMPUTE_PORT`, `COMPUTE_KEY`).

```sh
val() { grep "^$1=" research.local.env | cut -d= -f2- | tr -d '\r"'; }
H=$(val COMPUTE_HOST); PORT=$(val COMPUTE_PORT); PORT=${PORT:-22}; KEY=$(val COMPUTE_KEY)
C=research/code/certify
ssh -p "$PORT" -i "$KEY" "$H" 'mkdir -p ~/calib'
scp -P "$PORT" -i "$KEY" "$C/box_gap_calib.py" "$C/box_gap_calib_node45.sh" research/code/lattice_generator.py "$H":calib/
ssh -p "$PORT" -i "$KEY" "$H" 'cd ~/calib && nohup sh box_gap_calib_node45.sh pilot > pilot.log 2>&1 &'
# after the pilot: read pilot.log (selftest PASS, beta=0 rq = 1,2,3,4, hot/cold plaquettes agree), then
ssh -p "$PORT" -i "$KEY" "$H" 'cd ~/calib && nohup sh box_gap_calib_node45.sh core > core.log 2>&1 &'
# watch it take two cores at nice 19 and no more:
ssh -p "$PORT" -i "$KEY" "$H" 'ps -eo pid,user,ni,pcpu,rss,etimes,args --sort=-pcpu | head; free -g'
```

The logged `lattice_generator` sha256 should read `d0eef5da…fde003`, the workstation copy at `8247cda`.

Outputs are written to `~/calib`:

- `{tier}_j{1,2}.csv`: one row per estimator, family, observable and lag.
- `*.provenance.json`: host, versions, hashes, arguments and per-point timings.
- `raw/*.npz`: per-boundary aggregates, so the analysis can be rerun without regenerating.
