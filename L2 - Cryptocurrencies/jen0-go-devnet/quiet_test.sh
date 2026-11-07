#!/usr/bin/env bash
# Quiet-network test (Jen-0.5): 5 honest nodes. Normal traffic for T1 s, then
# every wallet stops for T2 s (no transfers at all), then traffic resumes for
# T3 s. Without tickets the minting gate would stop the chain in the quiet part;
# with tickets, minters keep blocks coming and keep earning new coins.
set -uo pipefail
cd "$(dirname "$0")"
T1=${T1:-90}; T2=${T2:-180}; T3=${T3:-60}
mkdir -p logs results
PORTS=(7401 7402 7403 7404 7405)
BLOW=(4 5 6 7 8)
SEAL=(40000 50000 60000 70000 80000)
peers_except() { local out=""; for p in "${PORTS[@]}"; do [ "$p" != "$1" ] && out+="127.0.0.1:$p,"; done; echo "${out%,}"; }
pids=()
for i in 0 1 2 3 4; do
  ./jen05 node --id $i --n 5 --port ${PORTS[$i]} --peers "$(peers_except ${PORTS[$i]})" --keys keys \
    --claims=true --grace=true --blowrate ${BLOW[$i]} --sealrate ${SEAL[$i]} > logs/quiet$i.log 2>&1 &
  pids+=($!)
done
trap 'kill ${pids[@]} 2>/dev/null || true' EXIT
sleep $T1
t_quiet=$(date +%s%3N)
for p in "${PORTS[@]}"; do curl -s "http://127.0.0.1:$p/admin/traffic?on=0" >/dev/null; done
echo "== $T1 s: all wallets stop sending"
sleep $T2
t_back=$(date +%s%3N)
for p in "${PORTS[@]}"; do curl -s "http://127.0.0.1:$p/admin/traffic?on=1" >/dev/null; done
echo "== $((T1+T2)) s: traffic resumes"
sleep $T3
python3 tools/quiet.py 7401 $t_quiet $t_back
echo
./jen05 report --ports 7401,7402,7403,7404,7405 | sed -n '1,12p'
