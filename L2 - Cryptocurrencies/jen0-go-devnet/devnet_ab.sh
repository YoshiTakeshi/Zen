#!/usr/bin/env bash
# Jen-0.10 devnet A/B: the same binary with the Jen-0.9 rules (RULE=purity:
# purity alone moves the cap, no leaf quota, no fee pool, no split payment
# pool) or the Jen-0.10 balanced rules (RULE=balanced).
#
#   TEST=load  light traffic until height 30, then ten times more payments
#              than the minters can prove, until height 90
#   TEST=big   node 0 proves 15x faster than the others, mines most blocks
#              and puts its own leaves first (--selfish); heavy traffic to height 60
#
# Proving is simulated (--fakeprove ms per leaf) so 6 nodes fit on one small
# machine. Devnet-scaled controller: cap +3% / -1.2% per block, fullness
# average 1/4 per block (the real chain: +0.3% / -0.12%, about 1/29).
# Usage: RULE=balanced TEST=load ./devnet_ab.sh
set -uo pipefail
cd "$(dirname "$0")"
RULE=${RULE:-balanced}; TEST=${TEST:-load}; N=${N:-6}; BASE=${BASE:-8100}
FAKE=${FAKE:-1500}
mkdir -p logs results
if [ "$RULE" = balanced ]; then RFLAGS="--balanced=true --split=true"; else RFLAGS="--balanced=false --split=false"; fi
peers_of() {
  local i=$1 out=""
  for o in 1 2 3; do j=$(( (i+o) % N )); [ $j -ne $i ] && out+="127.0.0.1:$((BASE+j)),"; done
  echo "${out%,}" | tr ',' '\n' | sort -u | paste -sd, -
}
TXMS0=1500; END=90; SWITCH=30
if [ "$TEST" = big ]; then TXMS0=150; END=60; SWITCH=0; fi
pids=()
for ((i=0;i<N;i++)); do
  MINE=false; [ $i -lt 3 ] && MINE=true
  EXTRA="--fakeprove $FAKE --sealrate 60000"
  if [ "$TEST" = big ] && [ $i -eq 0 ]; then EXTRA="--fakeprove 100 --sealrate 240000 --selfish=true"; fi
  ./jen10 node --id $i --n $N --port $((BASE+i)) --peers "$(peers_of $i)" --keys keys \
    --users 600 --grace=true --blowmem 1 --blowrate 6 --mine=$MINE $EXTRA \
    --leafcap 16 --fast 0 --slow 0 --feebid=true --txms $TXMS0 --cwstep 10 \
    --capgrow 300 --capshrink 120 --fullema 4 --credblocks 30 $RFLAGS \
    > logs/ab_${TEST}_${RULE}_$i.log 2>&1 &
  pids+=($!)
done
trap 'kill ${pids[@]} 2>/dev/null || true' EXIT
height() { curl -s --max-time 5 http://127.0.0.1:$((BASE+1))/status | python3 -c 'import json,sys; print(json.load(sys.stdin)["height"])' 2>/dev/null || echo 0; }
switched=0
start=$(date +%s)
while true; do
  h=$(height)
  if [ "$TEST" = load ] && [ $switched -eq 0 ] && [ "$h" -ge $SWITCH ]; then
    for ((i=0;i<N;i++)); do curl -s "http://127.0.0.1:$((BASE+i))/admin/txms?ms=150" >/dev/null; done
    switched=1; echo "height $h: traffic x10"
  fi
  [ "$h" -ge $END ] && break
  [ $(( $(date +%s) - start )) -gt 3600 ] && { echo "timeout at height $h"; break; }
  sleep 5
done
sleep 3
OUT=results/ab_${TEST}_${RULE}.json
python3 - "$BASE" "$N" "$OUT" <<'PY'
import json, sys, urllib.request
base, n, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
get = lambda p, path: json.load(urllib.request.urlopen("http://127.0.0.1:%d%s" % (p, path), timeout=60))
chain = get(base + 1, "/chain")
sts = []
for i in range(n):
    try:
        sts.append(get(base + i, "/status"))
    except Exception as e:
        sts.append({"error": str(e)})
json.dump({"chain": chain, "status": sts}, open(out, "w"))
print("saved", out, "blocks", len(chain))
PY
