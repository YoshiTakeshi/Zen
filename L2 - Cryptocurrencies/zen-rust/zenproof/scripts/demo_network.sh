# Stage 9 live demo: channel peers talk over the network. A payment, a crash that loses an update (the peer's signed state heals it),
# a joint close negotiated over the wire, and a watchtower folder that fills by itself.
cd "$(dirname "$0")/.."
Z=target/release/zenproof; W=/tmp/t3/wallets; R=/tmp/netd
pkill -x zenproof; sleep 1; rm -rf /tmp/t3 $R; mkdir -p $R/alice $R/bob $R/tower
$Z net init all /tmp/t3 >/dev/null
(nohup $Z node serve-all /tmp/t3 > /tmp/t3.log 2>&1 &); sleep 4
mine(){ $Z node mine 127.0.0.1:$1 $2 2>&1 | grep RESULT >/dev/null; }
K=127.0.0.1:18441,127.0.0.1:18461
bal(){ $Z wallet balance $W/$1.key 127.0.0.1:18441 | cut -d'|' -f2 | tr -d ' '; }
mine 18451 3
A=$($Z wallet address $W/w2.key); B=$($Z wallet address $W/w3.key); PB=$($Z wallet pubkey $W/w3.key)
$Z chan open $W/w2.key $K $B $PB 500000000 3 >/dev/null; mine 18451 2
$Z chan adopt $R/a.chan $W/w2.key $K $B >/dev/null; $Z chan join $R/b.chan $W/w3.key $K $A >/dev/null
cp $W/w2.key $R/alice/wallet.key; cp $W/w3.key $R/bob/wallet.key
conf(){ printf "name $1\nlisten 127.0.0.1:$2\nchain ken 127.0.0.1:18461 127.0.0.1:18441\nprice ken 1\nfee_ppm 0\nfee_base 0\nmargin_secs 120\n$3" > $R/$1/node.conf; }
conf alice 19201 ""; conf bob 19202 "tower_dir $R/tower\n"
$Z rnode add-channel $R/alice $R/a.chan 127.0.0.1:19202 >/dev/null; $Z rnode add-channel $R/bob $R/b.chan 127.0.0.1:19201 >/dev/null
for d in alice bob; do (nohup $Z rnode run $R/$d > $R/$d.log 2>&1 &); done; sleep 2
st(){ $Z rnode status $R/$1 | python3 -c "import sys,json; [print('  $1: update',c['update'],'mine',c['mine'],'theirs',c['theirs']) for c in json.load(sys.stdin)['channels']]"; }
echo "== Alice pays Bob 100 000 000 over the wire"
$Z rnode pay $R/alice "$($Z rnode invoice $R/bob 100000000 2)" | tail -1; st alice; st bob
echo "== the tower folder was filled by Bob's node: $(ls $R/tower | wc -l) file, at update $(grep '^seq' $R/tower/*.chan)"
echo "== Alice's machine crashes and comes back with an OLD copy of her channel (update 0); Bob is at update 2"
CF=$(ls $R/alice/channels/*.chan); cp $CF /tmp/netd/now.chan
pkill -f "rnode run $R/alice" 2>/dev/null || true
sed -i 's/^seq .*/seq 0/; s/^bal_a .*/bal_a 500000000/' $CF
(nohup $Z rnode run $R/alice > $R/alice.log 2>&1 &); sleep 1
echo "before sync:"; st alice
$Z rnode sync $R/alice; echo "after sync:"; st alice
echo "== a stranger on the wire: a plain request to Bob's channel port is refused (the same request from this machine, as the CLI, is local control only)"
python3 - <<PY
import socket,json
s=socket.create_connection(("127.0.0.1",19202)); s.sendall((json.dumps({"t":"sync","chan":"$(basename $CF .chan)","seq":0})+"\n").encode()); print(" ->", s.makefile().readline().strip())
PY
echo "== Alice and Bob close the channel together, over the network (both sign); no waiting window"
ID=$(basename $CF .chan | cut -c1-8)
$Z rnode close $R/alice $ID; mine 18451 2
echo "alice $(bal w2) | bob $(bal w3) (bob gained exactly 100 000 000; the channel is gone: $(curl -s http://127.0.0.1:18461/api/channels | python3 -c 'import sys,json; print(json.load(sys.stdin)["count"])') on chain)"
pkill -x zenproof
