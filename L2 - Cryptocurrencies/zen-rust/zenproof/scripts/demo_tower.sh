# Stage 7 live demo: a watchtower defends an offline channel owner against an old-state close.
cd "$(dirname "$0")/.."
Z=target/release/zenproof; W=/tmp/t3/wallets; D=/tmp/twr
pkill -x zenproof; sleep 1; rm -rf /tmp/t3 $D; mkdir -p $D/tower
$Z net init all /tmp/t3 >/dev/null
(nohup $Z node serve-all /tmp/t3 > /tmp/t3.log 2>&1 &); sleep 4
mine(){ $Z node mine 127.0.0.1:$1 $2 2>&1 | grep RESULT >/dev/null; }
K=127.0.0.1:18441,127.0.0.1:18461
bal(){ $Z wallet balance $W/$1.key 127.0.0.1:18441 | cut -d'|' -f2 | tr -d ' '; }
mine 18451 3
A=$($Z wallet address $W/w2.key); B=$($Z wallet address $W/w3.key); PB=$($Z wallet pubkey $W/w3.key)
$Z chan open $W/w2.key $K $B $PB 500000000 3 >/dev/null; mine 18451 2
$Z chan join $D/b.chan $W/w3.key $K $A >/dev/null
cp $D/b.chan $D/a.chan; sed -i 's/^role b/role a/' $D/a.chan
pay(){ P=$($Z chan pay $D/$1.chan $W/$3.key $4); ACK=$($Z chan accept $D/$2.chan $W/$5.key $P); $Z chan commit $D/$1.chan $ACK; }
pay a b w2 100000000 w3                      # update 1: Alice pays Bob 100 000 000
cp $D/a.chan $D/a.old                        # Alice keeps this copy, which is good for her (she has 400 000 000 in it)
pay a b w2 150000000 w3                      # update 2: Alice pays Bob 150 000 000 more (Bob has 250 000 000 now)
# the update-1 copy is Alice's; she will try to use it
echo "== Bob goes offline after handing his newest state to a watchtower (wallet w0, which holds none of his coins)"
cp $D/b.chan $D/tower/bob.chan
(nohup $Z chan watch $D/tower $W/w0.key $K > $D/tower.log 2>&1 &)
echo "== Alice cheats: posts the OLDER update 1, where she still has 400 000 000"
$Z chan dispute $D/a.old $W/w2.key $K >/dev/null; mine 18451 2
sleep 4; mine 18451 2
cat $D/tower.log
echo "== the window runs out; the tower settles"
mine 18451 4; sleep 4; mine 18451 2
cat $D/tower.log
echo "Bob's balance (10 000 000 000 + his newest share 250 000 000, less nothing: the tower paid the fees): $(bal w3)"
curl -s http://127.0.0.1:18461/api/channels | python3 -c "import sys,json; print('channels left on chain:', json.load(sys.stdin)['count'])"
pkill -x zenproof
