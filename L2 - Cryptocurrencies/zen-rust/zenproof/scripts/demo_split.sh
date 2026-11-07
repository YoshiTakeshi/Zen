# Stage 13 live demo: the three chains run as three SEPARATE processes (as on three machines) and follow each other over the network.
# A cross-chain trade (Ken coins for Yen coins) is still claimed with the other chain's proof, checked against headers that came over the wire.
cd "$(dirname "$0")/.."
Z=target/release/zenproof; D=/tmp/split; W=$D/wallets
pkill -x zenproof; sleep 1; rm -rf $D
$Z net init all $D >/dev/null
# each chain's public file names where its full nodes are (here: this machine, three ports)
echo "seed 127.0.0.1:18440" >> $D/yen/net.conf; echo "seed 127.0.0.1:18441" >> $D/ken/net.conf; echo "seed 127.0.0.1:18442" >> $D/jen/net.conf
for c in yen ken jen; do (nohup $Z node serve-chain $D $c > $D/$c.log 2>&1 &); done; sleep 6
mine(){ $Z node mine 127.0.0.1:$1 $2 2>&1 | grep RESULT >/dev/null; }
for p in 18450 18451 18452; do mine $p 3; done; sleep 4
echo "== Ken's explorer: Yen and Jen are followed over the network"
curl -s http://127.0.0.1:18461/api/chains | python3 -c "import sys,json; [print(' ',c['name'], 'height', c['height'], '(own node)' if c['self'] else '(checked header by header over the network)') for c in json.load(sys.stdin)]"
KEN=127.0.0.1:18441,127.0.0.1:18461; YEN=127.0.0.1:18440,127.0.0.1:18460
addr(){ $Z wallet address $W/$1.key; }
echo "== w0 sells 200 000 000 Ken for 100 000 000 Yen; w2 takes it, pays on Yen, claims on Ken with the Yen proof"
$Z wallet order-make $W/w0.key $KEN 200000000 1 100000000 $(addr w0) 1000 10 >/dev/null; mine 18451 2
L=$(curl -s http://127.0.0.1:18461/api/orders | python3 -c "import sys,json; print(json.load(sys.stdin)['orders'][0]['lock'])")
$Z wallet order-reserve $W/w2.key $KEN $L >/dev/null; mine 18451 2
$Z wallet pay $W/w2.key 127.0.0.1:18440 $(addr w0) 100000000 >/dev/null; mine 18450 5; sleep 4
L=$(curl -s http://127.0.0.1:18461/api/orders | python3 -c "import sys,json; print([o['lock'] for o in json.load(sys.stdin)['orders'] if o['state']=='reserved'][-1])")
$Z wallet order-claim $W/w2.key $KEN $L $YEN >/dev/null; mine 18451 2
echo "orders left on Ken: $(curl -s http://127.0.0.1:18461/api/orders | python3 -c 'import sys,json; print(json.load(sys.stdin)["count"])') | fills on tape: $(curl -s http://127.0.0.1:18461/api/fills | python3 -c 'import sys,json; print(json.load(sys.stdin)["count"])')"
pkill -x zenproof
