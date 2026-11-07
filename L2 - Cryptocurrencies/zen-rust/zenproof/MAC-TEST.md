# Testing Zen on a MacBook (Apple Silicon, 24 GB) — Justus L. Ludovic

Written in the Linux sandbox; **not yet run on macOS**. Everything here uses ordinary TCP on your own machine (no I2P, no Tor), with stand-in stamps unless you do part 4. If a step fails, send me the message.

## 1. Install (once)
```
xcode-select --install                                   # compiler tools, if not already there
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source "$HOME/.cargo/env"
```
Unzip the project, then `cd zkbench/zenproof`.

## 2. Build
```
export RUSTC_BOOTSTRAP=1          # plonky2 needs it; put it in ~/.zshrc to keep it
cargo build --release             # a few minutes
```
The binary is `target/release/zenproof`. (The x86-only CPU flags in `.cargo/config.toml` are skipped on Apple Silicon.)

## 3. Run the three-chain test network
```
Z=target/release/zenproof
$Z net init all /tmp/zen-net                 # makes keys and network files (test keys, no value)
$Z node serve-all /tmp/zen-net               # Yen, Ken, Jen in one process; leave it running
```
Open http://127.0.0.1:18461/ (Ken explorer; Yen 18460, Jen 18462). In a second Terminal tab, mine blocks and send a payment:
```
Z=target/release/zenproof; W=/tmp/zen-net/wallets
for p in 18450 18451 18452; do $Z node mine 127.0.0.1:$p 3; done
$Z wallet address $W/w1.key
$Z wallet pay $W/w0.key 127.0.0.1:18442 <address of w1> 1000000
$Z node mine 127.0.0.1:18452 2
$Z wallet balance $W/w1.key 127.0.0.1:18442
```
Ready-made live demos (orders, auctions, channels, factories, routing, watchtower): `bash scripts/demo_market.sh`, `demo_channels_1.sh`, `demo_factory.sh`, `demo_routing.sh`, `demo_network.sh`, `demo_tower.sh`. They use `/tmp` and stop any running `zenproof` first.

Or use the container (Docker Desktop, arm64): `docker build -t zen .` then `docker run -d --name zen -p 127.0.0.1:18440-18462:18440-18462 -v zen-data:/data zen`. See `DOCKER.md`.

## 4. The whole test suite (optional)
```
cargo test --release
```
About 25 minutes on 2 cores in the sandbox; expect less on an M4. Expected: 137 passed, 0 failed, 2 ignored.

## 5. Real Groth16 stamps (optional, heavy)
Needs Go 1.26.8 or newer (`brew install go`) and about 6 GB of RAM for setup, 2 GB of disk for the proving key (your 24 GB is enough).
1. Build the prover as in `../g16wrap/README.md` (apply the patch, copy `zenwrap/main.go`, `go build -o zenwrap ./cmd/zenwrap`).
2. Make the key for the current circuit: the circuit files are in `out_v7/`; run `zenwrap compile` and `zenwrap setup` on that folder as in `README.md` (Round 54: about 17 minutes in the sandbox). The proving key is not in the zip (2 GB).
3. Run the node with `ZEN_G16=<folder with zen.pk, zen.r1cs, zen.vk> ZEN_WRAP=<path to zenwrap> $Z node serve ...`. Each block then takes minutes to prove; `out_v7/zen.vk` alone is enough for a node that only checks stamps. This key is single-party and for testing only.
Skip this part unless you want to see real stamps; steps 1 to 4 test the rules, wallets, channels, orders and the network.

## 6. Keep it running 24/7 and have your own wallet
**Your wallet** (the secret key is one small file; whoever has it owns the coins; back it up, never share it):
```
mkdir -p ~/zen/wallet
Z=target/release/zenproof
$Z wallet new ~/zen/wallet/me.key        # prints your address; never overwrites an existing file
$Z wallet address ~/zen/wallet/me.key
$Z wallet balance ~/zen/wallet/me.key 127.0.0.1:18442     # Jen (18441 Ken, 18440 Yen)
```
Test coins come from the test wallets in `~/zen/net/wallets/` (for example `w0.key`): `$Z wallet pay ~/zen/net/wallets/w0.key 127.0.0.1:18442 <your address> 1000000`. These coins have no value.

**Run it:** `bash scripts/run-forever.sh` starts all three chains and mines a block on each every 20 s (change with `ZEN_BLOCK_SECS=60`). All data is in `~/zen` (not `/tmp`), so a restart continues the same chains. Close the terminal tab or press Ctrl+C to stop.

**Start by itself and restart after a crash or reboot (launchd):**
```
mkdir -p ~/zen ~/Library/LaunchAgents
sed -e "s|REPLACE_ME|$(cd .. && pwd)|" -e "s|REPLACE_HOME|$HOME|" scripts/com.zen.node.plist > ~/Library/LaunchAgents/com.zen.node.plist
launchctl load ~/Library/LaunchAgents/com.zen.node.plist
```
Stop it with `launchctl unload ~/Library/LaunchAgents/com.zen.node.plist`; the log is `~/zen/zen.log`. The `caffeinate` in the file keeps the Mac from idle-sleeping while the node runs, but a closed lid or a battery drain still sleeps it: for true 24/7 keep it plugged in and set System Settings > Battery > Options > "Prevent automatic sleeping on power adapter when the display is off". Do not move the project folder after loading.

Back up `~/zen` (at least `~/zen/wallet`). Remember: this is a test network, the keys are test keys, and the single-party setup and the stand-in stamps mean it is not a place for value.

## 7. Wallet in the browser
With the network running (step 3 or 6), in a second terminal tab:
```
cargo build --release                       # once, to get the new command
target/release/zenproof wallet web ~/zen/wallet/me.key
```
Open http://127.0.0.1:18470/ . The page shows your address (with a Copy button), your balance on Jen, Ken and Yen (refreshed every 10 s), a Send form (chain, address, amount in grams; the 1% fee is added) and links to the three explorers. Pick another port with a last argument: `wallet web <key file> 18471`; a second key file in a second tab gives a second wallet. The key stays in the file: the page only talks to the wallet program on this computer, which listens on 127.0.0.1 only, answers only to `localhost`/`127.0.0.1`, and signs a payment only for a request carrying the token it put into the page. Stop it with Ctrl+C. Not shown yet: payment history and orders/channels (use the explorer and the command line for those).
