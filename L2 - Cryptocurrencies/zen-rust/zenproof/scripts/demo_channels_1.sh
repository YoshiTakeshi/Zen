set -e
cd /home/claude/zkbench/zenproof
Z=target/release/zenproof; W=/tmp/t3/wallets; D=/tmp/chd
rm -rf /tmp/t3 $D; mkdir -p $D
$Z net init all /tmp/t3 >/dev/null
(nohup $Z node serve-all /tmp/t3 > /tmp/t3.log 2>&1 &); sleep 4
mine(){ $Z node mine 127.0.0.1:$1 $2 2>&1 | grep RESULT; }
bal(){ $Z wallet balance $W/$1.key $2 | cut -d'|' -f2; }
K=127.0.0.1:18441,127.0.0.1:18461
mine 18451 3
A=$($Z wallet address $W/w2.key); B=$($Z wallet address $W/w3.key); PB=$($Z wallet pubkey $W/w3.key)
echo "== open a two-party channel on Ken: w2 funds 500000000, window 3 blocks"
$Z chan open $W/w2.key $K $B $PB 500000000 3
mine 18451 1
$Z chan join $D/b.chan $W/w3.key $K $A
cp $D/b.chan $D/a.chan; sed -i 's/^role b/role a/' $D/a.chan
$Z chan show $D/a.chan
echo "== payments off chain"
P=$($Z chan pay $D/a.chan $W/w2.key 100000000); ACK=$($Z chan accept $D/b.chan $W/w3.key $P); $Z chan commit $D/a.chan $ACK
P=$($Z chan pay $D/a.chan $W/w2.key 50000000);  ACK=$($Z chan accept $D/b.chan $W/w3.key $P); $Z chan commit $D/a.chan $ACK
P=$($Z chan pay $D/b.chan $W/w3.key 30000000);  ACK=$($Z chan accept $D/a.chan $W/w2.key $P); $Z chan commit $D/b.chan $ACK
$Z chan show $D/a.chan; $Z chan show $D/b.chan
echo "== b cheats: posts update 1 (older); a answers with the newest inside the window"
cp $D/b.chan $D/b.latest
