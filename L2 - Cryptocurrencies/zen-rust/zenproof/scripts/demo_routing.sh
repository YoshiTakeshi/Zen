cd /home/claude/zkbench/zenproof
Z=target/release/zenproof; W=/tmp/t3/wallets; R=/tmp/rt
pkill -x zenproof; sleep 1
rm -rf /tmp/t3 $R; mkdir -p $R
$Z net init all /tmp/t3 >/dev/null
(nohup $Z node serve-all /tmp/t3 > /tmp/t3.log 2>&1 &); sleep 4
mine(){ $Z node mine 127.0.0.1:$1 $2 2>&1 | grep RESULT; }
Y=127.0.0.1:18440,127.0.0.1:18460; K=127.0.0.1:18441,127.0.0.1:18461; J=127.0.0.1:18442,127.0.0.1:18462
mine 18450 2; mine 18451 2; mine 18452 2
addr(){ $Z wallet address $W/$1.key; }; pub(){ $Z wallet pubkey $W/$1.key; }
# Alice=w0 S=w1 T=w2 Carol=w3
echo "== channels: Alice-S on Jen (Alice funds), S-T on Ken (S funds), T-Carol on Yen (T funds)"
$Z chan open $W/w0.key $J $(addr w1) $(pub w1) 1000000000 3
$Z chan open $W/w1.key $K $(addr w2) $(pub w2) 1000000000 3
$Z chan open $W/w2.key $Y $(addr w3) $(pub w3) 2000000000 3
mine 18450 2; mine 18451 2; mine 18452 2
mkdir -p $R/alice $R/s $R/t $R/carol
for n in alice:w0 s:w1 t:w2 carol:w3; do d=${n%%:*}; w=${n##*:}; cp $W/$w.key $R/$d/wallet.key; done
# files: funder side role a, other side role b
$Z chan join $R/s_jen.chan $W/w1.key $J $(addr w0);  cp $R/s_jen.chan $R/alice_jen.chan; sed -i 's/^role b/role a/' $R/alice_jen.chan
$Z chan join $R/t_ken.chan $W/w2.key $K $(addr w1);  cp $R/t_ken.chan $R/s_ken.chan; sed -i 's/^role b/role a/' $R/s_ken.chan
$Z chan join $R/carol_yen.chan $W/w3.key $Y $(addr w2); cp $R/carol_yen.chan $R/t_yen.chan; sed -i 's/^role b/role a/' $R/t_yen.chan
conf(){ cat > $R/$1/node.conf <<EOF
name $1
listen 127.0.0.1:$2
chain yen 127.0.0.1:18460 127.0.0.1:18440
chain ken 127.0.0.1:18461 127.0.0.1:18441
chain jen 127.0.0.1:18462 127.0.0.1:18442
price yen 10
price ken 3
price jen 1
fee_ppm 2000
spread_ppm 5000
fee_base 1
margin_secs 120
EOF
}
conf alice 19001; conf s 19002; conf t 19003; conf carol 19004
$Z rnode add-channel $R/alice $R/alice_jen.chan 127.0.0.1:19002
$Z rnode add-channel $R/s $R/s_jen.chan 127.0.0.1:19001
$Z rnode add-channel $R/s $R/s_ken.chan 127.0.0.1:19003
$Z rnode add-channel $R/t $R/t_ken.chan 127.0.0.1:19002
$Z rnode add-channel $R/t $R/t_yen.chan 127.0.0.1:19004
$Z rnode add-channel $R/carol $R/carol_yen.chan 127.0.0.1:19003
for d in alice s t carol; do (nohup $Z rnode run $R/$d > $R/$d.log 2>&1 &); done; sleep 2
echo "== Carol makes an invoice for 2000000 Yen units"
INV=$($Z rnode invoice $R/carol 2000000 1); echo $INV
echo "== Alice pays it: Jen -> Ken -> Yen"
$Z rnode pay $R/alice $INV
sleep 1
for d in alice s t carol; do echo "--- $d"; $Z rnode status $R/$d | python3 -c "import sys,json; v=json.load(sys.stdin); [print(' chan',c['id'],'chain',c['chain'],'update',c['update'],'mine',c['mine'],'theirs',c['theirs'],'locks',c['locks']) for c in v['channels']]"; done
echo "$INV" > $R/inv.txt
