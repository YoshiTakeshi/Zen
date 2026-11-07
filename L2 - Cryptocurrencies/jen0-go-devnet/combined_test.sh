#!/usr/bin/env bash
# Jen-0.11 combined test: the Sen peg, the balanced resize and attacks together.
# 6 nodes, simulated proving (1.5 s a leaf). A Sen is worth SEN base units
# outside the chain; W starts at 3 Sen.
#   A  h 1-30    normal traffic, 30% of payments priced in Sen
#   B  h 31-60   traffic x10 (fees climb)
#   C  h 61-100  node 0 attacks: proves 15x faster, puts its own leaves first,
#                and sends fake JEN-mode payments (goods "worth" 60 Sen) to its
#                own users, 3x as often as an honest node
#   D  h 101-140 attack over; the Sen is now worth 1.5x as many base units
# RULES=jen11: equal-weight peg window, fullness against block time, grow > 90%
# RULES=jen10: the Jen-0.10 settings (peg window by value, fullness = leaves / cap, grow > 80%)
set -uo pipefail
cd "$(dirname "$0")"
RULES=${RULES:-jen11}; N=6; BASE=${BASE:-8500}; SEN=20
mkdir -p logs results
if [ "$RULES" = jen11 ]; then RF="--pegequal=true --fulltime=true --fullgrow 900"; else RF="--pegequal=false --fulltime=false --fullgrow 800"; fi
peers_of() {
  local i=$1 out=""
  for o in 1 2 3; do j=$(( (i+o) % N )); [ $j -ne $i ] && out+="127.0.0.1:$((BASE+j)),"; done
  echo "${out%,}" | tr ',' '\n' | sort -u | paste -sd, -
}
pids=()
for ((i=0;i<N;i++)); do
  MINE=false; [ $i -lt 3 ] && MINE=true
  SR=60000; [ $i -eq 0 ] && SR=120000
  ./jen11 node --id $i --n $N --port $((BASE+i)) --peers "$(peers_of $i)" --keys keys \
    --users 600 --grace=true --blowmem 1 --blowrate 6 --mine=$MINE --fakeprove 1500 --sealrate $SR \
    --leafcap 16 --fast 0 --slow 0 --feebid=true --txms 1500 \
    --capgrow 300 --capshrink 120 --fullema 4 --credblocks 30 --balanced=true --split=true \
    --sen $SEN --jenpct 30 --kmed 2 --cwgenesis $((3*SEN)) --cwstep 3 $RF \
    > logs/comb_${RULES}_$i.log 2>&1 &
  pids+=($!)
done
trap 'kill ${pids[@]} 2>/dev/null || true' EXIT
P() { curl -s --max-time 5 "http://127.0.0.1:$((BASE+$1))$2" >/dev/null; }
all() { for ((i=0;i<N;i++)); do P $i "$1"; done; }
height() { curl -s --max-time 5 http://127.0.0.1:$((BASE+1))/status | python3 -c 'import json,sys; print(json.load(sys.stdin)["height"])' 2>/dev/null || echo 0; }
snap() { curl -s --max-time 10 http://127.0.0.1:$BASE/status > results/comb_${RULES}_snap_$1.json; }
phase=A; start=$(date +%s)
while true; do
  h=$(height)
  if [ $phase = A ] && [ "$h" -ge 30 ]; then all "/admin/txms?ms=150"; phase=B; echo "h $h: B traffic x10"; fi
  if [ $phase = B ] && [ "$h" -ge 60 ]; then
    snap B
    P 0 "/admin/fakeprove?ms=100"; P 0 "/admin/selfish?on=1"; P 0 "/admin/jen?pct=100"; P 0 "/admin/kmed?sen=60"
    P 0 "/admin/selfpay?on=1"; P 0 "/admin/txms?ms=50"
    phase=C; echo "h $h: C attack"
  fi
  if [ $phase = C ] && [ "$h" -ge 100 ]; then
    snap C
    P 0 "/admin/fakeprove?ms=1500"; P 0 "/admin/selfish?on=0"; P 0 "/admin/jen?pct=30"; P 0 "/admin/kmed?sen=2"
    P 0 "/admin/selfpay?on=0"; P 0 "/admin/txms?ms=150"
    all "/admin/sen?units=$((SEN*3/2))"
    phase=D; echo "h $h: D attack over, Sen worth $((SEN*3/2)) base units"
  fi
  [ "$h" -ge 140 ] && break
  [ $(( $(date +%s) - start )) -gt 4200 ] && { echo "timeout at height $h"; break; }
  sleep 4
done
sleep 3
snap D
python3 - "$BASE" "$N" "results/comb_${RULES}.json" <<'PY'
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
