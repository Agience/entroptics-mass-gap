"""Collect the cell-view influence reads (cellview_influence.py JSON outputs) into one summary and print its
tables.

    python cellview_summary.py IN_DIR OUT.json
For each read: per truncation level the TV row (sup and cross-fit, jackknife errors), its null, its margin
against 1 in units of its error, the W1 row (extreme pair and sup), the range tests and the pair correlations;
for a Gaussian control the exact rows; the 2nd and 6th moments.
"""
import glob
import json
import os
import sys


def margin(v, e):
    # DERIVED: the margin is in units of the error, so a zero error leaves it undefined (division guard)
    return (1.0 - v) / e if e > 0 else float("nan")


if __name__ == "__main__":
    src, out = sys.argv[1], sys.argv[2]
    summ = {}
    for f in sorted(glob.glob(os.path.join(src, "*.json"))):
        d = json.load(open(f))
        name = os.path.basename(f)[:-5]
        rows = {}
        for lv, r in d["levels"].items():
            D, N = r["data"], r["null"]
            rows[lv] = {
                "L": r["L"], "n_centres": r["n_centres"],
                "tv_sup": [D["sup"], D["sup_err"]], "tv_xfit": [D["xfit"], D["xfit_err"]],
                "tv_null": [N["sup"], N["xfit"]],
                "sigma_below_1_sup": margin(D["sup"], D["sup_err"]),
                "sigma_below_1_xfit": margin(D["xfit"], D["xfit_err"]),
                "w1_extreme": [r["w1_data"]["extreme"], r["w1_data"]["extreme_err"]],
                "w1_sup": [r["w1_data"]["sup"], r["w1_data"]["sup_err"]],
                "w1_null_extreme": r["w1_null"]["extreme"],
                "range_diag": r["range_dg"], "range_axis2": r.get("range_a2"),
                "corr": {k: v["corr"] for k, v in r["pairs"].items()},
                "exact": r.get("exact"),
            }
        summ[name] = {"nconf": d["nconf"], "m": d["m"], "groups": d["groups"], "blocks": d["blocks"],
                      "control": d["control"], "moments": d["moments"], "levels": rows}
        print(f"\n{name}  nconf={d['nconf']} m={d['m']} groups={d['groups']} control={d['control'] or '-'}")
        mo = d["moments"]
        print("  moments centred <x^2>={:.4g}+-{:.2g} <x^6>={:.4g}+-{:.2g}; raw <e^2>={:.4g}+-{:.2g} <e^6>={:.4g}+-{:.2g}"
              .format(*mo["centred_m2"], *mo["centred_m6"], *mo["raw_m2"], *mo["raw_m6"]))
        for lv, r in rows.items():
            ex = r["exact"]
            print("  {:8s} L={:7.3f} TV sup {:.3f}+-{:.3f} xfit {:.3f}+-{:.3f} null {:.3f}/{:.3f} | W1 ext {:.3f}+-{:.3f} "
                  "sup {:.3f}+-{:.3f} null {:.3f} | diag {:.3f}/{:.3f} corr_t {:.3f} corr_2t {:.3f}{}".format(
                      lv, r["L"], *r["tv_sup"], *r["tv_xfit"], *r["tv_null"], *r["w1_extreme"], *r["w1_sup"],
                      r["w1_null_extreme"], r["range_diag"]["data"], r["range_diag"]["null"], r["corr"]["t"],
                      r["corr"]["2t"],
                      "" if not ex else " | exact TV sup {:.3f}".format(ex["binned_sup"])))
    json.dump(summ, open(out, "w"), indent=1)
