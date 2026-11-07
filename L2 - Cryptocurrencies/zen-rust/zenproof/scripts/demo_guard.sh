# Stage 11 live demo: a peer goes silent while a point lock is open. Alice's node closes the channel on chain by itself, in time, and gets her coins back.
cd "$(dirname "$0")/.."
Z=target/release/zenproof; W=/tmp/t3/wallets; R=/tmp/grd
pkill -x zenproof; sleep 1; rm -rf /tmp/t3 $R; mkdir -p $R/alice
$Z net init all /tmp/t3 >/dev/null
(nohup $Z node serve-all /tmp/t3 > /tmp/t3.log 2>&1 &); sleep 4
mine(){ $Z node mine 127.0.0.1:$1 $2 2>&1 | grep RESULT >/dev/null; }
K=127.0.0.1:18441,127.0.0.1:18461
bal(){ $Z wallet balance $W/$1.key 127.0.0.1:18441 | cut -d'|' -f2 | tr -d ' '; }
height(){ curl -s http://127.0.0.1:18461/api/status | python3 -c "import sys,json; print(json.load(sys.stdin)['height'])"; }
mine 18451 3
A=$($Z wallet address $W/w2.key); B=$($Z wallet address $W/w3.key); PB=$($Z wallet pubkey $W/w3.key)
$Z chan open $W/w2.key $K $B $PB 500000000 3 >/dev/null; mine 18451 2
$Z chan adopt $R/a.chan $W/w2.key $K $B >/dev/null; $Z chan join $R/b.chan $W/w3.key $K $A >/dev/null
echo "alice at the start: $(bal w2)"
# Alice locks 200 000 000 for Bob behind a point nobody here knows the scalar of; Bob accepts and then disappears
EXP=$(( $(height) + 14 ))
PT=$($Z wallet pubkey $W/w0.key)
P=$($Z chan lock $R/a.chan $W/w2.key 200000000 $PT $EXP); ACK=$($Z chan accept $R/b.chan $W/w3.key $P); $Z chan commit $R/a.chan $ACK
echo "== the lock (200 000 000, runs out at Ken block $EXP) is in Alice's channel; Bob's node is gone"
cp $W/w2.key $R/alice/wallet.key; mkdir -p $R/alice/channels; $Z rnode add-channel $R/alice $R/a.chan 127.0.0.1:19999 >/dev/null
printf "name alice\nlisten 127.0.0.1:19301\nchain ken 127.0.0.1:18461 127.0.0.1:18441\nprice ken 1\nguard_blocks 6\nguard_wait 5\n" > $R/alice/node.conf
(nohup $Z rnode run $R/alice > $R/alice.log 2>&1 &); sleep 8
echo "== blocks come; the lock gets near its expiry (height $(height))"
mine 18451 3; sleep 6; mine 18451 3; sleep 6
echo "== the window runs; then the lock's time is over and the node settles"
mine 18451 8; sleep 8; mine 18451 3; sleep 5; mine 18451 2
grep guard $R/alice.log | sed 's/^\[alice\] //' | cut -c1-150 | awk '!s[$0]++' | head -8
echo "alice at the end: $(bal w2) (the 200 000 000 came back; the rest is fees) | bob: $(bal w3) (untouched)"
curl -s http://127.0.0.1:18461/api/channels | python3 -c "import sys,json; print('channels left on chain:', json.load(sys.stdin)['count'])"
pkill -x zenproof
