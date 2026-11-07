#!/usr/bin/env bash
# Entry point of the Zen image.
#   testnet       (default) the three-chain testnet: makes the network files in /data/net on the first start, then serves Yen, Ken and Jen.
#                 ZEN_AUTOMINE=1 (default in the image) also mines a block on each chain every ZEN_BLOCK_SECS seconds (stand-in stamps: no heavy hardware).
#   chain <yen|ken|jen>   ONE chain as its own container; the other two are followed over the network (ZEN_FOLLOW_YEN / _KEN / _JEN = host:p2p port, comma list).
#                 The network files (net.conf per chain, minters) must be in $ZEN_NET_DIR; with ZEN_INIT=1 and no files yet they are made (single host / demo).
#   healthcheck   exit 0 when the Ken API answers (used by the container's HEALTHCHECK)
#   shell         a shell, for looking around
#   <anything else>  passed to zenproof (wallet, chan, rnode, market ...), e.g.  docker exec zen zenproof wallet balance ...
set -euo pipefail
NET=${ZEN_NET_DIR:-/data/net}
BASE=${ZEN_BASE_PORT:-18440}

case "${1:-testnet}" in
  healthcheck)
    exec 3<>/dev/tcp/127.0.0.1/$((BASE + 20 + ${ZEN_HEALTH_IDX:-1}))
    printf 'GET /api/status HTTP/1.0\r\nHost: localhost\r\n\r\n' >&3
    read -r line <&3
    [[ "$line" == *" 200"* ]] ;;
  shell) exec bash ;;
  chain)
    NAME=${2:?usage: chain <yen|ken|jen>}
    case "$NAME" in yen) IDX=0;; ken) IDX=1;; jen) IDX=2;; *) echo "chain must be yen, ken or jen"; exit 2;; esac
    if [ ! -f "$NET/$NAME/net.conf" ]; then
      if [ "${ZEN_INIT:-0}" = "1" ]; then
        # several containers may start at once on a shared volume: the first to take the lock makes the files, the others wait
        mkdir -p "$NET"
        if mkdir "$NET/.init.lock" 2>/dev/null; then zenproof net init all "$NET.tmp" && cp -a "$NET.tmp/." "$NET/" && rm -rf "$NET.tmp"; touch "$NET/.init.done"; fi
        for _ in $(seq 1 120); do [ -f "$NET/.init.done" ] && break; sleep 1; done
      else
        echo "no $NET/$NAME/net.conf: copy the network files here (or set ZEN_INIT=1 for a throw-away testnet)"; exit 2
      fi
    fi
    zenproof node serve-chain "$NET" "$NAME" "$BASE" &
    SERVER=$!
    trap 'kill $SERVER 2>/dev/null; exit 0' TERM INT
    if [ "${ZEN_AUTOMINE:-0}" = "1" ]; then
      sleep 6
      ( while kill -0 $SERVER 2>/dev/null; do
          zenproof node mine "127.0.0.1:$((BASE + 10 + IDX))" 1 >/dev/null 2>&1 || true
          sleep "${ZEN_BLOCK_SECS:-20}"
        done ) &
    fi
    wait $SERVER ;;
  testnet)
    if [ ! -d "$NET/ken" ]; then
      echo "first start: making the testnet files in $NET (testnet keys, no value)"
      zenproof net init all "$NET"
    fi
    zenproof node serve-all "$NET" "$BASE" &
    SERVER=$!
    trap 'kill $SERVER 2>/dev/null; exit 0' TERM INT
    if [ "${ZEN_AUTOMINE:-0}" = "1" ]; then
      sleep 6
      ( while kill -0 $SERVER 2>/dev/null; do
          for off in 10 11 12; do zenproof node mine "127.0.0.1:$((BASE + off))" 1 >/dev/null 2>&1 || true; done
          sleep "${ZEN_BLOCK_SECS:-20}"
        done ) &
    fi
    wait $SERVER ;;
  *) exec zenproof "$@" ;;
esac
