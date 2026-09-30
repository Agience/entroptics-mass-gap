"""8_3_run_nobump_refnull.py -- K_signal across each group's coupling range with a PER-GROUP
confined reference null. For each gauge group a strong-coupling reference ensemble of the same group,
generated on the same lattice (so the same 8x8 plane shape), sets the null; K_signal is then read on
fresh configs across the coupling range against that null, each value with its same-marginal control
(every plane's values permuted within the plane, config i seeded by its index) and the paired
difference.

Reads come through the single typed wrapper (research/code/entroptics_adapter.py): the null is
`confined_reference_null` built from `confined_top_singular_values` of the reference ensemble and
tagged with the plane shape it was calibrated at, passed to `confinement(config, null=...)`, which
refuses a plane of another shape. GPU generation, CPU reads. Writes 8_3_dat_nobump.csv,
8_3_dat_su3_nobump.csv, 8_4_dat_disorder_response.csv and 8_3_dat_confinement_order_parameter.csv.

NOTE: this is NOT the owner of any of those four (see research/regen_all.py); it is an exploratory
path, not the reproduction one. For the first three the schema differs from the owner's, so a stray
run is caught as a shape change. For 8_3_dat_confinement_order_parameter.csv it does NOT: the
columns are the owner's exactly (beta, dims, K_signal, K_signal_err, phase, n), so a stray run
overwrites the committed artifact with different values and the same shape, which `regen_all
--verify` reports as moved cells rather than as a wrong producer. Run this only when that is what
you intend, and re-run the owner afterwards.

    python 8_3_run_nobump_refnull.py --device cuda
"""
from __future__ import annotations
import argparse, os, sys
import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(_HERE, "..", "code")))
import entroptics_adapter as entroptics                 # the wrapper (reference_null lives here + in the library)
import lattice_generator as generator
import table

LAT = (8, 8, 8, 16)
# deeply-confined reference coupling per group (SU(N) confined at every beta; U(1) below beta_c~1.01)
REF_BETA = {"u1": 0.70, "su2": 1.00, "su3": 5.20}
THERM = {"u1": 15, "su2": 25, "su3": 80}
METHOD = {"u1": "metropolis", "su2": "heatbath", "su3": "heatbath"}
BETAS = {
    "u1":  [round(x, 2) for x in np.arange(0.40, 1.75, 0.10)],
    "su2": [round(x, 2) for x in np.arange(0.50, 4.45, 0.25)],
    "su3": [round(x, 2) for x in np.arange(5.00, 7.05, 0.20)],
}
BETA_C = 1.01


def gen(group, beta, n, device, seed):
    fb = generator.config_batch(LAT, float(beta), group=group, n=n, therm=THERM[group],
                                seed=seed, device=device, method=METHOD[group])
    a = fb.detach().cpu().numpy().astype(np.float32)
    return [a[i] for i in range(a.shape[0])]


def build_ref_null(group, device, n_ref, far):
    """The confined-reference null: floor = center + z(far)*scale from the reference ensemble's
    top singular values (`confined_reference_null`, O(1), sharpens analytically to any `far`)."""
    ref = gen(group, REF_BETA[group], n_ref, device, seed=777)
    svs = entroptics.confined_top_singular_values(ref)
    return entroptics.confined_reference_null(svs, far=far, plane_shape=(LAT[0], LAT[1]))


def sweep(group, device, n, n_ref, far):
    null = build_ref_null(group, device, n_ref, far)
    rows = []
    for beta in BETAS[group]:
        cfgs = gen(group, beta, n, device, seed=1000 * int(beta * 100))
        K = np.array([entroptics.confinement(c, null=null) for c in cfgs], float)
        S = np.array([entroptics.confinement(c, null=null, shuffle=i) for i, c in enumerate(cfgs)], float)
        D = K - S                                             # paired per configuration
        H = np.array([entroptics.marginal_entropy(c) for c in cfgs], float)
        rows.append(dict(group=group, beta=beta, dims="x".join(map(str, LAT)),
                         confinement=float(K.mean()), confinement_err=float(K.std() / np.sqrt(n)),
                         confinement_shuffled=float(S.mean()),
                         confinement_shuffled_err=float(S.std() / np.sqrt(n)),
                         confinement_minus_shuffled=float(D.mean()),
                         confinement_minus_shuffled_err=float(D.std() / np.sqrt(n)),
                         H=float(H.mean()), H_err=float(H.std() / np.sqrt(n)), n=n))
        print(f"  {group} b={beta:5.2f}  K={K.mean():.4f}+/-{K.std()/np.sqrt(n):.4f}  H={H.mean():.4f}", flush=True)
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--device", default="cuda")
    ap.add_argument("--n", type=int, default=400)
    ap.add_argument("--n-ref", type=int, default=400)
    ap.add_argument("--far", type=float, default=0.05)
    args = ap.parse_args()
    print(f"reference-null no-bump: n={args.n} n_ref={args.n_ref} far={args.far} ref_betas={REF_BETA}", flush=True)

    allrows = {g: sweep(g, args.device, args.n, args.n_ref, args.far) for g in ("u1", "su2", "su3")}
    nb = allrows["u1"] + allrows["su2"]
    shuf = ["confinement_shuffled", "confinement_shuffled_err", "confinement_minus_shuffled",
            "confinement_minus_shuffled_err"]
    table.write(os.path.join(_HERE, "8_3_dat_nobump.csv"), nb,
                ["group", "beta", "dims", "confinement", "confinement_err", "H", "H_err", "n"] + shuf)
    table.write(os.path.join(_HERE, "8_3_dat_su3_nobump.csv"), allrows["su3"],
                ["group", "beta", "dims", "confinement", "confinement_err", "H", "H_err", "n"] + shuf)
    table.write(os.path.join(_HERE, "8_4_dat_disorder_response.csv"),
                [dict(group=r["group"], beta=r["beta"], dims=r["dims"], H=r["H"], H_err=r["H_err"], n=r["n"]) for r in nb],
                ["group", "beta", "dims", "H", "H_err", "n"])
    # U(1) fine crossing rows for 8_3_dat_confinement_order_parameter.csv
    cop = [dict(beta=r["beta"], dims=r["dims"], K_signal=r["confinement"], K_signal_err=r["confinement_err"],
                phase=("confined" if r["beta"] < BETA_C else "Coulomb"), n=r["n"],
                **{"K_signal" + k[len("confinement"):]: r[k] for k in shuf}) for r in allrows["u1"]]
    table.write(os.path.join(_HERE, "8_3_dat_confinement_order_parameter.csv"), cop,
                ["beta", "dims", "K_signal", "K_signal_err", "phase", "n", "K_signal_shuffled",
                 "K_signal_shuffled_err", "K_signal_minus_shuffled", "K_signal_minus_shuffled_err"])
    print("REFNULL-NOBUMP-DONE  (figures: python research/regen_all.py --phase figures)", flush=True)


if __name__ == "__main__":
    main()
