#!/usr/bin/env bash
# Runs a Jen-0 devnet on one machine: 5 honest nodes with different minting
# power + 1 attacker, for DURATION seconds, then prints the report.
#
#   ./run_devnet.sh [DURATION_SECONDS]
set -euo pipefail
cd "$(dirname "$0")"
DURATION=${1:-420}
N=6
[ -x ./jen0 ] || go build -o jen0 .
[ -f keys/leaf.pk ] || ./jen0 setup --keys keys
mkdir -p logs
PORTS=(7001 7002 7003 7004 7005 7006)
BLOW=(2000 3000 4000 5000 6000 0)      # minter power differs per node (fairness test)
SEAL=(40000 50000 60000 70000 80000 0) # miner power differs too
peers_except() { local out=""; for p in "${PORTS[@]}"; do [ "$p" != "$1" ] && out+="127.0.0.1:$p,"; done; echo "${out%,}"; }
pids=()
for i in 0 1 2 3 4 5; do
  EVIL=false; [ $i -eq 5 ] && EVIL=true
  ./jen0 node --id $i --n $N --port ${PORTS[$i]} --peers "$(peers_except ${PORTS[$i]})" \
    --keys keys --blowrate ${BLOW[$i]} --sealrate ${SEAL[$i]} --evil=$EVIL > logs/node$i.log 2>&1 &
  pids+=($!)
done
trap 'kill ${pids[@]} 2>/dev/null || true' EXIT
echo "devnet running for $DURATION s (logs in ./logs)..."
sleep "$DURATION"
./jen0 report --ports 7001,7002,7003,7004,7005,7006
