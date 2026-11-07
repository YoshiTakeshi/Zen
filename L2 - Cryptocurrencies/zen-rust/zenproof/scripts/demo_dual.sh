# Stage 8 live demo: a dual-funded channel. a puts in 300 000 000, b adds 200 000 000, then both can pay each other from their own side.
cd "$(dirname "$0")/.."
Z=target/release/zenproof; W=/tmp/t3/wallets; D=/tmp/dual
pkill -x zenproof; sleep 1; rm -rf /tmp/t3 $D; mkdir -p $D
$Z net init all /tmp/t3 >/dev/null
(nohup $Z node serve-all /tmp/t3 > /tmp/t3.log 2>&1 &); sleep 4
mine(){ $Z node mine 127.0.0.1:$1 $2 2>&1 | grep RESULT >/dev/null; }
K=127.0.0.1:18441,127.0.0.1:18461
bal(){ $Z wallet balance $W/$1.key 127.0.0.1:18441 | cut -d'|' -f2 | tr -d ' '; }
mine 18451 3
A=$($Z wallet address $W/w2.key); B=$($Z wallet address $W/w3.key); PB=$($Z wallet pubkey $W/w3.key)
echo "before: a $(bal w2) | b $(bal w3)"
$Z chan open $W/w2.key $K $B $PB 300000000 3 >/dev/null; mine 18451 2
$Z chan fund $W/w3.key $K $A 200000000; mine 18451 2
$Z chan adopt $D/a.chan $W/w2.key $K $B; $Z chan join $D/b.chan $W/w3.key $K $A
pay(){ P=$($Z chan pay $D/$1.chan $W/$3.key $4); ACK=$($Z chan accept $D/$2.chan $W/$5.key $P); $Z chan commit $D/$1.chan $ACK; }
echo "== b pays a 150 000 000 from the coins b put in; a pays b 50 000 000"
pay b a w3 150000000 w2
pay a b w2 50000000 w3
$Z chan show $D/a.chan | head -8
echo "== a closes on chain with the newest state, waits the window, settles"
$Z chan dispute $D/a.chan $W/w2.key $K >/dev/null; mine 18451 6
$Z chan settle $D/a.chan $W/w2.key $K >/dev/null; mine 18451 2
echo "after: a $(bal w2) (expected +100 000 000 less fees) | b $(bal w3) (expected -100 000 000 less fees)"
pkill -x zenproof
