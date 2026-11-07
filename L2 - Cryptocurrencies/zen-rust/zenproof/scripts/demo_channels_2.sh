cd /home/claude/zkbench/zenproof
Z=target/release/zenproof; W=/tmp/t3/wallets; D=/tmp/chd
mine(){ $Z node mine 127.0.0.1:$1 $2 2>&1 | grep RESULT; }
bal(){ $Z wallet balance $W/$1.key $2 | cut -d'|' -f2; }
K=127.0.0.1:18441,127.0.0.1:18461; J=127.0.0.1:18442,127.0.0.1:18462
A=$($Z wallet address $W/w2.key); B=$($Z wallet address $W/w3.key); PB=$($Z wallet pubkey $W/w3.key)
echo "balances now: w2 $(bal w2 127.0.0.1:18441) | w3 $(bal w3 127.0.0.1:18441)"
echo "== cooperative close at the current state"
SB=$($Z chan close-sign $D/b.chan $W/w3.key)
$Z chan close $D/a.chan $W/w2.key $K $SB
mine 18451 1
echo "after close: w2 $(bal w2 127.0.0.1:18441) | w3 $(bal w3 127.0.0.1:18441)"
echo "== second channel; b tries an old state"
rm -f $D/a2.chan $D/b2.chan
$Z chan open $W/w2.key $K $B $PB 200000000 3; mine 18451 1
$Z chan join $D/b2.chan $W/w3.key $K $A; cp $D/b2.chan $D/a2.chan; sed -i 's/^role b/role a/' $D/a2.chan
P=$($Z chan pay $D/a2.chan $W/w2.key 120000000); ACK=$($Z chan accept $D/b2.chan $W/w3.key $P); $Z chan commit $D/a2.chan $ACK
cp $D/b2.chan $D/b2.old
P=$($Z chan pay $D/b2.chan $W/w3.key 100000000); ACK=$($Z chan accept $D/a2.chan $W/w2.key $P); $Z chan commit $D/b2.chan $ACK
echo "newest: $($Z chan show $D/a2.chan | cut -d'|' -f4-5)"
echo "b posts the OLD state (update 1: b has 120000000)"
$Z chan dispute $D/b2.old $W/w3.key $K; mine 18451 1
echo "a answers with the newest state (update 2: b has 20000000)"
$Z chan dispute $D/a2.chan $W/w2.key $K; mine 18451 1
echo "b tries the old one again:"; $Z chan dispute $D/b2.old $W/w3.key $K 2>&1 | head -2; mine 18451 1
mine 18451 4
before2=$(bal w2 127.0.0.1:18441); before3=$(bal w3 127.0.0.1:18441)
$Z chan settle $D/a2.chan $W/w2.key $K; mine 18451 1
echo "settled: w2 $before2 -> $(bal w2 127.0.0.1:18441) | w3 $before3 -> $(bal w3 127.0.0.1:18441)  (expected w2 +180000000 -fee, w3 +20000000 -fees)"
echo "== a stream on Jen: w0 pays w1 per use, one number signed by w0 alone"
mine 18452 2
A0=$($Z wallet address $W/w0.key); A1=$($Z wallet address $W/w1.key); P1=$($Z wallet pubkey $W/w1.key)
$Z chan open $W/w0.key $J $A1 $P1 100000000 3 oneway; mine 18452 1
$Z chan join $D/rx.stream $W/w1.key $J $A0; cp $D/rx.stream $D/tx.stream; sed -i 's/^role b/role a/' $D/tx.stream
for i in 1 2 3 4 5; do M=$($Z chan pay $D/tx.stream $W/w0.key 10000000); $Z chan commit $D/rx.stream $M >/dev/null; done
$Z chan show $D/rx.stream
echo "w1 (receiver) closes with the latest signed amount"
b1=$(bal w1 127.0.0.1:18442)
$Z chan dispute $D/rx.stream $W/w1.key $J; mine 18452 5
$Z chan settle $D/rx.stream $W/w1.key $J; mine 18452 1
echo "w1: $b1 -> $(bal w1 127.0.0.1:18442)  (expected +50000000 less two fees)"
grep -i "invalid\|refus" /tmp/t3.log | tail -3
