#!/usr/bin/env bash
# Runs the three-chain test network and mines a block on each chain every ZEN_BLOCK_SECS seconds (stand-in stamps).
# Data lives in ~/zen (change with ZEN_HOME): chains, test keys, wallets. Stop with Ctrl+C or `launchctl unload` (see MAC-TEST.md).
set -u
cd "$(dirname "$0")/.."
Z="$PWD/target/release/zenproof"
HOME_DIR=${ZEN_HOME:-$HOME/zen}; NET=$HOME_DIR/net; BASE=${ZEN_BASE_PORT:-18440}; SECS=${ZEN_BLOCK_SECS:-20}
mkdir -p "$HOME_DIR"
[ -d "$NET/ken" ] || { echo "first start: making the test network in $NET"; "$Z" net init all "$NET"; }
"$Z" node serve-all "$NET" "$BASE" &
SERVER=$!
trap 'kill $SERVER 2>/dev/null; exit 0' TERM INT
sleep 6
while kill -0 $SERVER 2>/dev/null; do
  for off in 10 11 12; do "$Z" node mine "127.0.0.1:$((BASE + off))" 1 >/dev/null 2>&1 || true; done
  sleep "$SECS"
done
wait $SERVER
