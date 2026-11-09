"""Tables of the W1 influence row reads (cellview_w1.py outputs): per read and regressor set, the typical row
(centre-weighted mean over s0 in the 10-90% S quantiles) and the row at the S-quantile ends, every
bandwidth, the cross-fit (xfit) and cross-fit mean-slope (xmean) readings with jackknife errors, the
per-class split at the median s0, and the exact values of a control.

    python cellview_w1_summary.py OUT.json read1.json read2.json ...
"""
import json
import os
import sys

if __name__ == "__main__":
    out, files = sys.argv[1], sys.argv[2:]
    rep = {}
    for f in files:
        d = json.load(open(f))
        name = os.path.basename(f)[:-5]
        r = {"control": d["control"], "m": d["m"], "nconf": d["nconf"], "centres": d["centres"],
             "groups": d["groups"], "blocks": d["blocks"], "s0_quantiles": d["SQ"], "sets": {}}
        for s, byh in d["reads"].items():
            r["sets"][s] = {}
            for h, v in byh.items():
                su = v["summary"]
                mp = v["points"][len(v["points"]) // 2]
                e = {k: [su[k]["typ"], su[k]["typ_err"]] for k in ("xfit", "xmean", "upper")}
                e["profile_xfit"] = [[a, b] for a, b in zip(su["xfit"]["per_s0"], su["xfit"]["per_s0_err"])]
                e["classes_mid"] = {c: {"xfit": [mp["read"][c][1], mp["jk_err"][c][1]],
                                        "signed": [mp["read"][c][3], mp["jk_err"][c][3]]} for c in mp["read"]}
                if "exact" in su:
                    e["exact_typ"], e["exact_profile"] = su["exact"]["typ"], su["exact"]["per_s0"]
                r["sets"][s][h] = e
                prof = su["xfit"]
                print(f"{name:14s} {s:4s} h={h:5s} typ xfit {su['xfit']['typ']:.3f}+-{su['xfit']['typ_err']:.3f}"
                      f" xmean {su['xmean']['typ']:.3f}+-{su['xmean']['typ_err']:.3f}"
                      f" | q.02 {prof['per_s0'][0]:.2f}+-{prof['per_s0_err'][0]:.2f}"
                      f" q.5 {prof['per_s0'][len(prof['per_s0']) // 2]:.2f}"
                      f" q.98 {prof['per_s0'][-1]:.2f}+-{prof['per_s0_err'][-1]:.2f}"
                      + (f" | exact {su['exact']['typ']:.3f}" if "exact" in su else ""))
        rep[name] = r
    json.dump(rep, open(out, "w"), indent=1)
