#!/usr/bin/env bash
# Network-split test: 6 honest nodes. Together for T1 s, split into
# {0,1,2} and {3,4,5} for T2 s, reconnected for T3 s. Then checks that every
# node converged on one chain, how many blocks were abandoned, and that
# balances and supply agree everywhere.
set -euo pipefail
cd "$(dirname "$0")"
T1=${T1:-120}; T2=${T2:-210}; T3=${T3:-150}
mkdir -p logs results
PORTS=(7101 7102 7103 7104 7105 7106)
BLOW=(3000 3000 3000 5000 5000 5000)       # side B has more minting power
SEAL=(40000 40000 40000 70000 70000 70000) # and more mining power
addr() { echo "127.0.0.1:$1"; }
peers_except() { local out=""; for p in "${PORTS[@]}"; do [ "$p" != "$1" ] && out+="$(addr $p),"; done; echo "${out%,}"; }
pids=()
for i in 0 1 2 3 4 5; do
  ./jen0 node --id $i --n 6 --port ${PORTS[$i]} --peers "$(peers_except ${PORTS[$i]})" --keys keys \
    --blowrate ${BLOW[$i]} --sealrate ${SEAL[$i]} > logs/split$i.log 2>&1 &
  pids+=($!)
done
trap 'kill ${pids[@]} 2>/dev/null || true' EXIT
show() { for i in 0 1 2 3 4 5; do python3 tools/st.py ${PORTS[$i]}; done; }

echo "== phase 1: all connected for $T1 s"; sleep $T1; show
A="$(addr 7101),$(addr 7102),$(addr 7103)"; B="$(addr 7104),$(addr 7105),$(addr 7106)"
for i in 0 1 2; do curl -s "http://127.0.0.1:${PORTS[$i]}/admin/block?peers=$B" >/dev/null; done
for i in 3 4 5; do curl -s "http://127.0.0.1:${PORTS[$i]}/admin/block?peers=$A" >/dev/null; done
echo "== phase 2: split into {0,1,2} and {3,4,5} for $T2 s"; sleep $T2; show
for i in 0 1 2 3 4 5; do curl -s "http://127.0.0.1:${PORTS[$i]}/admin/block?peers=" >/dev/null; done
echo "== phase 3: reconnected for $T3 s"; sleep $T3; show
echo
echo "== reorganizations"
for i in 0 1 2 3 4 5; do python3 tools/st.py ${PORTS[$i]} full; done
echo
./jen0 report --ports 7101,7102,7103,7104,7105,7106 | sed -n '1,14p'
