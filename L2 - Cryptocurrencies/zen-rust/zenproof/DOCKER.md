# Running Zen from a container (Justus L. Ludovic)

One image runs the three-chain testnet (Yen, Ken, Jen) on Windows, macOS (Intel and Apple Silicon), Linux, a Raspberry Pi, a big server or a cluster. It is built for `linux/amd64` and `linux/arm64`; Docker picks the right one.

## Pull and run
```
docker run -d --name zen -p 127.0.0.1:18440-18462:18440-18462 -v zen-data:/data ghcr.io/OWNER/zen:latest
```
Then open http://localhost:18461/ (the Ken explorer; Yen is 18460, Jen 18462). The first start makes the testnet files (test keys, no value) in the `zen-data` volume; blocks are mined by themselves every 20 s per chain (stand-in stamps: no heavy hardware). Stop and start it as you like: it resumes from the volume.

Or with compose: `docker compose up -d` (file: `docker-compose.yml`). On Kubernetes: `kubectl apply -f k8s/zen.yaml`, then `kubectl -n zen port-forward svc/zen 18461:18461`.

## Using the node from outside
The tools are in the image: `docker exec zen zenproof wallet balance /data/net/wallets/w0.key 127.0.0.1:18441`, `... zenproof chan ...`, `... zenproof rnode ...`, `... zenproof market rates ...`.

## Settings (environment)
| variable | default in the image | meaning |
|---|---|---|
| `ZEN_AUTOMINE` | 1 | mine one block on each chain every `ZEN_BLOCK_SECS` |
| `ZEN_BLOCK_SECS` | 20 | seconds between automatic blocks |
| `ZEN_BIND` | 0.0.0.0 | address for p2p and Stratum inside the container |
| `ZEN_API_BIND`, `ZEN_API_BIND_ANY` | 0.0.0.0, 1 | the API listens on the container's address (a published port needs it) |
| `ZEN_API_HOSTS` | (empty) | extra names the API answers to (a gateway); it answers to `localhost` otherwise |
| `ZEN_NET_DIR`, `ZEN_BASE_PORT` | /data/net, 18440 | where the network files are, first port |

## Real proofs (optional)
The image's stand-in stamps carry no proof. To stamp blocks with the real 196-byte Groth16 proof, set `ZEN_G16` to a folder holding `zen.pk`, `zen.r1cs` and `zen.vk` and `ZEN_WRAP` to the `zenwrap` prover (about 2 GB of keys and minutes per block on 2 cores; see `README.md`, Rounds 54–55). A node that only checks stamps needs `zen.vk` alone (`out_v7/zen.vk`). The current setup is single-party and for tests only.

## Security
- Publish on the host's loopback (`127.0.0.1:` as above) unless you mean to open the node to a network. The API checks the Host name and a token for every write, but a testnet node is not hardened for the open internet.
- The keys made on first start are test keys inside the volume. Do not put value on them. Real wallet and minter keys belong in Secrets (Kubernetes) or a protected volume.
- The container runs as a non-root user; the Kubernetes file also drops all capabilities and uses a read-only root file system.

## Building it yourself
`docker build -t zen .` (the Rust build takes a few minutes), or for both CPUs: `docker buildx build --platform linux/amd64,linux/arm64 -t ghcr.io/OWNER/zen:latest --push .`. The workflow in `.github/workflows/docker.yml` does this on every tag and on main.

## One container per chain (cross-chain over the network)
`docker compose -f docker-compose.split.yml up -d` runs Yen, Ken and Jen as three containers (the `chain <name>` mode of the image). Each follows the other two over the network: `ZEN_FOLLOW_YEN`, `ZEN_FOLLOW_KEN`, `ZEN_FOLLOW_JEN` (comma lists of `host:p2p port`; or `seed` lines in the public net.conf) name their full nodes. On several machines, put the same network files (`yen|ken|jen/net.conf` and `minters/`) on each, start one chain per machine and point the variables at the other machines. A cross-chain trade is claimed with the other chain's proof, checked against headers that came over the wire.
