#!/usr/bin/env bash
# Hidden-chain attack test (Jen-0.5). 5 honest nodes + 1 attacker (node 5).
# The attacker takes part honestly for T1 s, then secretly builds its own chain
# for T2 s (it publishes nothing and ignores honest blocks), then releases it.
# Honest nodes switch to the attacker's chain only if it carries more weight.
#
#   ATTACK_SEAL  attacker sealing power (hashes/s; honest total is 300,000)
#   ATTACK_BLOW  attacker minting power (attempts per 10 s; honest total is 30; 0 = none)
#   TWOFACTOR    true (Jen-0.5 rule) or false (weigh seals only, Jen-0 rule)
set -uo pipefail
cd "$(dirname "$0")"
T1=${T1:-90}; T2=${T2:-240}; T3=${T3:-60}
ATTACK_SEAL=${ATTACK_SEAL:-900000}; ATTACK_BLOW=${ATTACK_BLOW:-0}; TWOFACTOR=${TWOFACTOR:-true}
mkdir -p logs results
PORTS=(7301 7302 7303 7304 7305 7306)
BLOW=(4 5 6 7 8 $ATTACK_BLOW)
SEAL=(40000 50000 60000 70000 80000 $ATTACK_SEAL)
peers_except() { local out=""; for p in "${PORTS[@]}"; do [ "$p" != "$1" ] && out+="127.0.0.1:$p,"; done; echo "${out%,}"; }
pids=()
for i in 0 1 2 3 4 5; do
  MINT=true; [ "${BLOW[$i]}" = "0" ] && MINT=false
  MINE=true; [ "${SEAL[$i]}" = "0" ] && MINE=false
  ./jen05 node --id $i --n 6 --port ${PORTS[$i]} --peers "$(peers_except ${PORTS[$i]})" --keys keys \
    --attacker 5 --claims=true --grace=true --twofactor=$TWOFACTOR --mint=$MINT --mine=$MINE \
    --blowrate ${BLOW[$i]} --sealrate ${SEAL[$i]} > logs/hidden$i.log 2>&1 &
  pids+=($!)
done
trap 'kill ${pids[@]} 2>/dev/null || true' EXIT
echo "hidden-chain attack: attacker sealing $ATTACK_SEAL/s (honest 300000/s), minting $ATTACK_BLOW attempts/10 s (honest 30), two-factor $TWOFACTOR"
sleep $T1
echo "== $T1 s: attacker starts its hidden chain"
python3 tools/attack.py 7301 7302 7303 7304 7305 7306 heights
curl -s http://127.0.0.1:7306/admin/fork >/dev/null
sleep $T2
echo "== $((T1+T2)) s: just before release"
python3 tools/attack.py 7301 7302 7303 7304 7305 7306 heights
curl -s http://127.0.0.1:7306/admin/release >/dev/null
sleep $T3
echo "== $((T1+T2+T3)) s: $T3 s after release"
python3 tools/attack.py 7301 7302 7303 7304 7305 7306 outcome
