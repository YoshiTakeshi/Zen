cd /home/claude/zkbench/zenproof
Z=target/release/zenproof; W=/tmp/t3/wallets; R=/tmp/rf
pkill -x zenproof; sleep 1
rm -rf /tmp/t3 $R; mkdir -p $R
$Z net init all /tmp/t3 >/dev/null
(nohup $Z node serve-all /tmp/t3 > /tmp/t3.log 2>&1 &); sleep 4
mine(){ $Z node mine 127.0.0.1:$1 $2 2>&1 | grep RESULT; }
K=127.0.0.1:18441,127.0.0.1:18461
addr(){ $Z wallet address $W/$1.key; }; pub(){ $Z wallet pubkey $W/$1.key; }
bal(){ $Z wallet balance $W/$1.key 127.0.0.1:18441 | cut -d'|' -f2 | tr -d ' ' ; }
mine 18451 3
# coordinator S=w1; members Alice=w0, Bob=w2, Carol=w3; 300 000 000 for each member's channel, one output on chain
echo "== one on-chain output for three members"
$Z chan factory-open $W/w1.key $K 3 $(addr w0) $(pub w0) 300000000  $(addr w2) $(pub w2) 300000000  $(addr w3) $(pub w3) 300000000
mine 18451 3
curl -s http://127.0.0.1:18461/api/channels | python3 -c "import sys,json; v=json.load(sys.stdin); print('channels seen by the API:', v['count'], '| factory:', v['channels'][0]['fid'][:8], '| on-chain outputs holding them:', len(set(c['lock'] for c in v['channels'])))"
for m in w0 w2 w3; do $Z chan adopt $R/s_$m.chan $W/w1.key $K $(addr $m); $Z chan join $R/${m}_s.chan $W/$m.key $K $(addr w1); done
echo "== Alice puts 200 000 000 of her own into her channel (so she can pay), Carol 0"
$Z chan factory-fund $W/w0.key $K $(addr w1) 200000000
mine 18451 3
for m in w0; do $Z chan adopt $R/s_$m.chan $W/w1.key $K $(addr $m); $Z chan join $R/${m}_s.chan $W/$m.key $K $(addr w1); done
mkdir -p $R/alice $R/s $R/carol
cp $W/w0.key $R/alice/wallet.key; cp $W/w1.key $R/s/wallet.key; cp $W/w3.key $R/carol/wallet.key
conf(){ cat > $R/$1/node.conf <<EOF
name $1
listen 127.0.0.1:$2
chain ken 127.0.0.1:18461 127.0.0.1:18441
price ken 1
fee_ppm 2000
fee_base 1
margin_secs 120
EOF
}
conf alice 19101; conf s 19102; conf carol 19103
$Z rnode add-channel $R/alice $R/w0_s.chan 127.0.0.1:19102
$Z rnode add-channel $R/s $R/s_w0.chan 127.0.0.1:19101
$Z rnode add-channel $R/s $R/s_w3.chan 127.0.0.1:19103
$Z rnode add-channel $R/carol $R/w3_s.chan 127.0.0.1:19102
for d in alice s carol; do (nohup $Z rnode run $R/$d > $R/$d.log 2>&1 &); done; sleep 2
echo "== Alice pays Carol 50 000 000 through the coordinator: two channels of ONE factory, nothing on chain"
INV=$($Z rnode invoice $R/carol 50000000 2)
$Z rnode pay $R/alice "$INV"
INV=$($Z rnode invoice $R/s 7000000 2)
$Z rnode pay $R/alice "$INV"
for d in alice s carol; do echo "--- $d"; $Z rnode status $R/$d | python3 -c "import sys,json; v=json.load(sys.stdin); [print(' chan',c['id'],'update',c['update'],'mine',c['mine'],'theirs',c['theirs'],'locks',c['locks']) for c in v['channels']]"; done
echo "== Carol leaves the factory on her own (post her latest state, wait the window, settle); Alice and Bob stay"
b3=$(bal w3); bs=$(bal w1)
$Z chan dispute $R/carol/channels/*.chan $W/w3.key $K; mine 18451 2
mine 18451 4
$Z chan settle $R/carol/channels/*.chan $W/w3.key $K; mine 18451 2
echo "carol: $b3 -> $(bal w3) (expected +50 000 000 less fees) | coordinator before $bs"
curl -s http://127.0.0.1:18461/api/channels | python3 -c "
import sys,json
v=json.load(sys.stdin)
for c in v['channels']: print(' member',c['idx'],c['state'],'capacity',c['capacity'])
print(' output on chain holds', sorted(set(c['lock'] for c in v['channels']))[0][:12], '...')"
echo "== Alice keeps paying through the same factory after Carol left"
INV=$($Z rnode invoice $R/s 3000000 2)
$Z rnode pay $R/alice "$INV"
$Z rnode status $R/alice | python3 -c "import sys,json; v=json.load(sys.stdin); [print(' alice chan',c['id'],'update',c['update'],'mine',c['mine'],'theirs',c['theirs']) for c in v['channels']]"
pkill -x zenproof
