#!/bin/sh
# Launch box_gap_calib.py on the shared compute node, from the directory holding this file, the
# script and a copy of lattice_generator.py. Every process is single-threaded and runs at nice 19;
# `core` and `full` run two such processes side by side and wait for both.
#
#   sh run_node45.sh pilot   # self-test, beta=0 control, beta=2.3 hot and cold (about 15 min)
#   sh run_node45.sh core    # 6 couplings, n = 2,3,4 at L = 8, L-check at 12 and 16 (about 5 h wall)
#   sh run_node45.sh full    # 11 couplings, L-check at 5 of them (about 11 h wall)
# Wall times are from workstation timings of one core; the pilot's provenance.json measures the node.
set -eu
cd "$(dirname "$0")"
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
PY="${PY:-$HOME/research-venv/bin/python}"
C="$PY -u box_gap_calib.py --lg-dir ."
TIER="${1:-pilot}"

case "$TIER" in
  pilot)
    nice -n 19 $C --selftest
    nice -n 19 $C --betas 0,2.3 --L 8 --n 2 --samples 40 --out pilot.csv
    nice -n 19 $C --betas 2.3 --L 8 --n 2 --samples 40 --start cold --out pilot_cold.csv
    ;;
  core|full)
    if [ "$TIER" = core ]; then
      B=0,1.5,2.0,2.3,2.5,3.0; BL=2.0,2.5
    else
      B=0,1.0,1.5,1.8,2.0,2.2,2.3,2.4,2.5,2.7,3.0; BL=1.5,2.0,2.3,2.5,3.0
    fi
    (
      nice -n 19 $C --betas $B --L 8 --n 2 --samples 200 --out "${TIER}_j1.csv" --save-raw raw
      nice -n 19 $C --betas $B --L 8 --n 4 --samples 200 --out "${TIER}_j1.csv" --save-raw raw
    ) > "${TIER}_j1.log" 2>&1 &
    (
      nice -n 19 $C --betas $B --L 8 --n 3 --samples 60 --inner-sweeps 100 --out "${TIER}_j2.csv" --save-raw raw
      nice -n 19 $C --betas $BL --L 12 --n 2 --boxes-per-axis 2 --samples 200 --out "${TIER}_j2.csv" --save-raw raw
      nice -n 19 $C --betas $BL --L 16 --n 2 --boxes-per-axis 2 --samples 200 --out "${TIER}_j2.csv" --save-raw raw
    ) > "${TIER}_j2.log" 2>&1 &
    wait
    ;;
  *)
    echo "usage: sh run_node45.sh pilot|core|full" >&2
    exit 2
    ;;
esac
