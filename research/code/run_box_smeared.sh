#!/bin/bash
# One slice of the smeared box series. Each GPU runs its own slice; the slices are disjoint.
#
# The series holds beta and the aperture FIXED and moves the box, which is the only way the
# measurement separates the box from anything else:
#
#     beta = 2.40   (one lattice spacing)      T = 32   (one aperture)      L varies   (the box)
#
# and does it at TWO smearing levels, so the smearing choice is hedged rather than bet on. Smearing
# is what lengthens the correlation length past one lattice spacing, which the unsmeared series
# could not do -- see certify/gap_of_box_operator.py.
#
# `--field operator` reduces each configuration to the zero-momentum history O(t), shape (n, T):
# kilobytes per shard instead of hundreds of megabytes, and the read's estimator dimension is then
# the moment-pencil ORDER rather than L^3, so growing the box no longer degrades the estimator. That
# is the whole reason this series can answer what the density series could not.
#
# JOBS is a space-separated list of `L:smear` pairs, so one script drives every card:
#
#     JOBS="24:32 16:32 12:16" bash run_box_smeared.sh
#
# The generator skips a shard that already exists, so a slice can be re-run safely and two slices
# that overlap cost time but cannot corrupt each other.
set -u
cd "$HOME/mg" || exit 1
OUT=${OUT:-/workspace/gen_boxsm}
BETA=${BETA:-2.40}
T=${T:-32}
N=${N:-96}
THERM=${THERM:-100}
mkdir -p "$OUT"

if [ -z "${JOBS:-}" ]; then
  echo "JOBS is empty: nothing to run. Set JOBS=\"L:smear L:smear ...\"" >&2
  exit 2
fi

echo "slice: JOBS=$JOBS  beta=$BETA T=$T n=$N therm=$THERM  out=$OUT"
for job in $JOBS; do
  L=${job%%:*}
  S=${job##*:}
  echo "=== L=$L smear=$S ==="
  python -u lattice_generator.py \
    --group su2 --L "$L" --T "$T" --betas "$BETA" --n "$N" --therm "$THERM" \
    --device cuda --method heatbath --fp 64 \
    --field operator --channel plaquette --smear "$S" \
    --seed $((2400000 + L)) --out "$OUT"
done
echo "done."
