# Stage 6 live demo: filled trades make the official rate; a batch auction decides who gets an order. Three chains, stand-in stamps.
cd "$(dirname "$0")/.."
Z=target/release/zenproof; W=/tmp/t3/wallets
pkill -x zenproof; sleep 1
rm -rf /tmp/t3; $Z net init all /tmp/t3 >/dev/null
(nohup $Z node serve-all /tmp/t3 > /tmp/t3.log 2>&1 &); sleep 4
mine(){ $Z node mine 127.0.0.1:$1 $2 2>&1 | grep RESULT >/dev/null; }
KEN=127.0.0.1:18441,127.0.0.1:18461; YEN=127.0.0.1:18440,127.0.0.1:18460; KAPI=127.0.0.1:18461
addr(){ $Z wallet address $W/$1.key; }
for p in 18450 18451 18452; do mine $p 3; done
lock_of(){ curl -s http://$KAPI/api/orders | python3 -c "
import sys,json
v=json.load(sys.stdin)['orders']; m='$1'; w=$2
print([o['lock'] for o in v if o['maker']==m and o['want_amount']==w and o['state'] in ('open','auction')][-1])"; }
# trade <maker> <taker> <sell on Ken> <price in Yen> [auction window]
trade(){
  M=$1; T=$2; S=$3; P=$4
  $Z wallet order-make $W/$M.key $KEN $S 1 $P $(addr $M) 1000 10 ${5:-0} >/dev/null; mine 18451 2
  L=$(lock_of $(addr $M) $P)
  if [ -n "$5" ]; then
    $Z wallet order-bid $W/$T.key $KEN $L $((S/100+1)) >/dev/null; mine 18451 $(( $5 + 2 ))
  else
    $Z wallet order-reserve $W/$T.key $KEN $L >/dev/null; mine 18451 2
  fi
  $Z wallet pay $W/$T.key 127.0.0.1:18440 $(addr $M) $P >/dev/null; mine 18450 5
  L=$(curl -s http://$KAPI/api/orders | python3 -c "import sys,json; print([o['lock'] for o in json.load(sys.stdin)['orders'] if o['state']=='reserved' and o['maker']=='$(addr $M)'][-1])")
  $Z wallet order-claim $W/$T.key $KEN $L 127.0.0.1:18440,127.0.0.1:18460 >/dev/null; mine 18451 2
}
echo "== two makers (w0, w1) sell Ken for Yen; two takers (w2, w3) buy. Nothing is announced: the tape is the trades."
trade w0 w2 200000000 100000000
echo "after 1 trade:"; curl -s http://$KAPI/api/rate
trade w1 w3 200000000 104000000
trade w0 w3 200000000 108000000
echo "after 3 trades from 2 makers and 2 takers:"; curl -s http://$KAPI/api/rate; echo
echo "== a batch order: the highest bid wins, a lower one is paid back at once"
$Z wallet order-make $W/w1.key $KEN 200000000 1 106000000 $(addr w1) 1000 10 4 >/dev/null; mine 18451 2
L=$(lock_of $(addr w1) 106000000)
$Z wallet order-bid $W/w2.key $KEN $L 2100000 >/dev/null; mine 18451 2
echo "w2 balance with its bid in:  $($Z wallet balance $W/w2.key 127.0.0.1:18441 | cut -d'|' -f2)"
L=$(lock_of $(addr w1) 106000000 2>/dev/null || curl -s http://$KAPI/api/orders | python3 -c "import sys,json; print([o['lock'] for o in json.load(sys.stdin)['orders'] if o['state']=='bidding'][-1])")
$Z wallet order-bid $W/w3.key $KEN $L 3500000 >/dev/null; mine 18451 2
echo "w2 balance after being outbid (escrow back):  $($Z wallet balance $W/w2.key 127.0.0.1:18441 | cut -d'|' -f2)"
curl -s http://$KAPI/api/orders | python3 -c "import sys,json; [print(' order',o['state'],'best bid',o['best_bid'],'taker',o['taker'][:12],'closes at',o['auction_close']) for o in json.load(sys.stdin)['orders'] if o['state']=='bidding']"
echo "== official rates (1 Ken in Yen), other pairs have no trades yet"
$Z market rates 127.0.0.1:18460 127.0.0.1:18461 127.0.0.1:18462
pkill -x zenproof
