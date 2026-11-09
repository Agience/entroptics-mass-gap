"""Collect influence_agg.py outputs into the row-sum table against the coarse spacing in r0.

For each read and block level: the coarse spacing 2^k a / r0 (r0/a from r0_read.py, the range quoted), the
TV row sum 18 C and the oscillation row sum 18 Cosc with their jackknife errors and their null floors, the
staple-sufficiency couplings, and the rectangle partners' linear-response share
    90 |eps_rect| sqrt((1 - E t^2)/3)
(18 rectangles x 5 links, each moving the tilt eps_rect <u, b> by at most 2 |eps_rect|, a TV of at most
|eps_rect| E|<u, e>| <= |eps_rect| sqrt((1 - E t^2)/3) per link).

With them, when the aggregate carries them: the jackknife bias-corrected row, the sample-size study with its
cross-fit row, and the rows inside the terciles of the two further neighbourhood scalars.

    python influence_summary.py OUT.json agg_*.json
"""
import json
import sys

import numpy as np

# r0/a read on the ensembles (r0_read.py; README of research/data/observer): low, high
R0A = {0.0: None, 0.05: None, 0.10: None, 2.30: (3.119, 3.119), 2.50: (6.03, 6.21), 2.70: (11.4, 11.9)}

rows = []
for path in sys.argv[2:]:
    r = json.load(open(path))
    beta, L, c = r["beta"], r["L"], r["c"]
    for lv in r["levels"]:
        k = lv["k"]
        sc = R0A.get(round(beta, 2))
        sp = None if sc is None else [2 ** k / sc[1], 2 ** k / sc[0]]
        c2 = np.array(lv["c_n_bins"]["c2"])
        et2 = float(np.mean((c2 + 1) / 4))
        ss = lv["staple_sufficiency"]
        rect_share = 90 * abs(ss["rect"]["eps"]) * np.sqrt(max(0.0, (1 - et2) / 3))
        rows.append({
            "read": path, "beta": beta, "L": L, "c": c, "k": k, "coarse_L": L // 2 ** k,
            "a_over_r0": sp, "links": lv["links"], "Nstar": lv["Nstar"], "mean_t": lv["mean_t"],
            "row18_tv": lv["row18"], "row18_tv_err": lv["row18_err"], "row18_tv_null": lv["row18_null"],
            "row18_osc": lv["row18osc"], "row18_osc_err": lv["row18osc_err"], "row18_osc_null": lv["row18osc_null"],
            "eps_rect": ss["rect"]["eps"], "eps_rect_err": ss["rect"]["eps_err"],
            "eps_adj": ss["adj"]["eps"], "eps_adj_err": ss["adj"]["eps_err"],
            "eps_rect_null": ss["rectN"]["eps"], "eps_adj_null": ss["adjN"]["eps"],
            "rect_share": rect_share,
            "exact": lv.get("exact"),
            "row18_bc": lv.get("row18_bc"),
            "size_study": lv.get("size_study"),
            "tercile_rows": lv.get("tercile_rows"),
        })
        e = rows[-1]
        print(f"b={beta:.2f} L={L} c={c} k={k} a/r0={'' if sp is None else f'{sp[0]:.2f}-{sp[1]:.2f}'} "
              f"TV {e['row18_tv']:.3f}+-{e['row18_tv_err']:.3f} (null {e['row18_tv_null']:.3f}) "
              f"osc {e['row18_osc']:.3f}+-{e['row18_osc_err']:.3f} (null {e['row18_osc_null']:.3f}) "
              f"rect {e['eps_rect']:+.4f}+-{e['eps_rect_err']:.4f} adj {e['eps_adj']:+.4f}+-{e['eps_adj_err']:.4f} "
              f"rect share {rect_share:.3f}"
              + (f" xfit {e['size_study'][-1]['row18_xfit_mean']:.3f}+-{e['size_study'][-1]['row18_xfit_sd']:.3f}"
                 if e["size_study"] else "")
              + "".join(f" {nm}[{v['unsplit']['row18']:.3f}: " + ",".join(f"{x['row18']:.3f}" for x in v["terciles"]) + "]"
                        for nm, v in (e["tercile_rows"] or {}).items()))
json.dump({"script": "influence_summary.py", "rows": rows}, open(sys.argv[1], "w"), indent=1)
