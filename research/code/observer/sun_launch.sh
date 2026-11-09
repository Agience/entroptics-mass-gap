#!/bin/sh
# SU(N) links campaigns on the CPU: one sun_campaign.py process per chain, at most WORKERS at once, nice 19,
# one BLAS thread; a launch waits while a Lean build (lake) runs on the host. Writes params.json per campaign
# before the chains and SHA256SUMS over the link shards after them.
#
#   sh sun_launch.sh ENS_ROOT N L "beta1 beta2 ..." chains therm nmeas gap seed0 WORKERS
set -e
root=$1; N=$2; L=$3; betas=$4; chains=$5; therm=$6; nmeas=$7; gap=$8; seed0=$9; workers=${10}
here=$(cd "$(dirname "$0")" && pwd)
py=${PY:-$HOME/research-venv/bin/python}
gen="$here/../lattice_generator.py"
jobs=""
for k in $(seq 0 $((chains - 1))); do
  for b in $betas; do
    camp="$root/su${N}_L${L}_b$(printf %.2f "$b")"
    mkdir -p "$camp"
    if [ ! -f "$camp/params.json" ]; then
      cat > "$camp/params.json" <<EOF
{
  "group": "su$N",
  "update": "heatbath (lattice_generator._sun_hb_sweep: Cabibbo-Marinari heat bath + 4 over-relaxation)",
  "dims": [$L, $L, $L, $L],
  "beta": $b,
  "chains": $chains,
  "starts": "chain k hot (k even, _sun_init) or cold (k odd, cold_init)",
  "therm": $therm,
  "nmeas": $nmeas,
  "gap": $gap,
  "seed0": $seed0,
  "seed_map": "lattice_generator.campaign_seed(seed0, beta, chain)",
  "backend": "numpy",
  "fp": "64 (generation), stored complex64",
  "layout": "links_c{k}_m{j}.npy: (1, x, y, z, t, direction, $N, $N) complex64",
  "generator": "$(readlink -f "$gen")",
  "generator_sha256": "$(sha256sum "$gen" | cut -d' ' -f1)",
  "campaign_script_sha256": "$(sha256sum "$here/sun_campaign.py" | cut -d' ' -f1)",
  "numpy": "$($py -c 'import numpy; print(numpy.__version__)')",
  "host": "$(hostname)",
  "started_utc": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
}
EOF
    fi
    jobs="$jobs $camp:$b:$k"
  done
done
echo $jobs | tr ' ' '\n' | xargs -P "$workers" -I{} sh -c '
  j={}; camp=${j%%:*}; rest=${j#*:}; b=${rest%%:*}; k=${rest#*:}
  while pgrep -x lake >/dev/null 2>&1; do sleep 60; done
  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 nice -n 19 '"$py"' '"$here"'/sun_campaign.py "$camp" '"$N $L"' "$b" "$k" '"$therm $nmeas $gap $seed0"' > "$camp/chain_c$k.log" 2>&1'
for b in $betas; do
  camp="$root/su${N}_L${L}_b$(printf %.2f "$b")"
  (cd "$camp" && sha256sum links_c*_m*.npy | sed 's/ \*/  /' > SHA256SUMS && touch DONE)
done
