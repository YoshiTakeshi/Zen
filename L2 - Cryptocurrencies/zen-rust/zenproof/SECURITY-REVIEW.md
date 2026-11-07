# Zen — security review, round 48 (Justus L. Ludovic)

An internal review of the whole protocol after stage 13. Method: read every consensus rule and every network entry point as an attacker would, write the attack as a test where it can be written, fix, and list what was not covered. This is **not** an outside audit and does not replace one.

## Findings

| # | Area | Severity | Finding | Fix | Test |
|---|------|----------|---------|-----|------|
| 1 | Consensus (`locks.rs`, `Run::one`) | High | The balance check for an operation was `bal < give + fee` in u64. With an amount near 2^64 the sum wraps, so a huge `give` could pass the check. (Later steps would usually still fail, but the check is the guard and must not rely on that.) | Computed in u128 | `an_amount_so_large_that_amount_plus_fee_wraps_is_refused` |
| 2 | Consensus (vaults) | Medium | The vault claim signature covered the lock and the destination but not the chain. A lock with the same terms on another chain has the same address, so a claim signed for one chain could be replayed on another. | The chain id is part of the signed message (`vault_claim_msg(chain, lock, dest)`) | `a_vault_claim_signed_for_one_chain_is_refused_on_another` |
| 3 | Transport (`transport.rs`, `route.rs`) | Medium | A sealed request could be sent again by a third party inside the 60 s time window. The answer stays secret, but a repeated request repeats its side effect. | Replay cache of the request's one-time key (kept two windows, capped at 100 000 entries; a full cache refuses) | `a_copy_of_a_request_inside_the_time_window_is_refused_but_a_new_request_is_not` |
| 4 | Routing daemon | Medium | (a) A peer's answer was read to the end of the line with no limit: one endless line fills memory. (b) The listener started a thread per connection with no cap, so many slow connections exhaust threads. | (a) answers limited to 4 MiB; (b) at most 64 connections at once, extra ones are dropped | Covered by the existing network/guard demos; limits are constants, not separately unit-tested |
| 5 | Cross-chain follower | Medium | The "best" chain among followed nodes was the one with most **blocks**. A chain with more blocks but less proof of work (easier difficulty) could win. | Headers carry cumulative work; the view is the chain with most work (height breaks ties) | `the_observer_keeps_the_longest_valid_chain…` now checks the work sum |

Checked and found sound (no change): money conservation in Make/Claim/Refund/Reserve/OrderClaim/Reopen/Return/Bid; channel start/update/settle/close/fund; factory fund/post/exit/exit-now (shares and point locks are bounded by the member's cap, so `cap - bal_c - locks` cannot go negative); account credit guards (`credit_to`: used slot, overflow); frame and body limits in p2p and the API; the signed state and close messages of channels and factories (they carry the chain id and a stable id); transport authentication (signature over E, S, C; MAC over all fields); channel authorization (caller must be the channel's peer).

## Known and accepted (documented, not fixed)

- **No forward secrecy for requests.** A request is sealed to the server's static key; if that key leaks later, recorded requests can be read. Answers are protected by an ephemeral key.
- **Replay cache is in memory.** After a restart a request from the last 60 s could be replayed once. Idempotent operations are unaffected.
- **`pay_to` reuse.** Several orders may name the same receiving address; the payment proof then fits any of them (the payment ntime must be after the order's `since`, and the amount must cover it). Makers should use a fresh address per order; the wallet does.
- **Official rate can be pushed by a Sybil trader.** Three fills from two makers and two takers are enough; each fill costs the 1% deposit and fees, but a rich attacker can move the rate for a while. Anything that relies on the rate (stream pricing) should treat it as a hint, not as an oracle. Raising the minimums or weighting by age are the options.
- **The fill tape is a view, not state.** It is rebuilt from blocks and not stored in snapshots, so a node that starts from a snapshot has fewer fills until it sees more.
- **Pool eviction.** A full operation pool refuses new operations; there is no replace-by-fee. Per-sender limit (4) and fee floor apply.
- **Guard clock.** The watchtower and the node guard use block height for deadlines, not wall time, but the stuck-timer for forced settlement uses the local clock.
- **Invalid-signature spam** costs a signature check each; peers sending it are banned by the p2p layer.

## Not covered — for an outside auditor

1. The zero-knowledge circuits. *Update, round 55:* at round 48 the new operations were not yet in the proof. Since rounds 49–55 they are (P1–P7), with an internal soundness battery (`src/soundness.rs`, 583 rule-breaking tries, 0 failures; it catches a deliberately removed rule). Still for an outside auditor: the circuits themselves, the rules left to the node by design (key subgroup, key/address binding, y sign, new-address uniqueness, distinct factory members, the foreign payment proof of an order claim), and the Groth16 setup, which is single-party and needs a public ceremony.
2. The elliptic-curve signature scheme and the hash-to-field mapping (`mint.rs`, `ec.rs`): constants, nonce generation, malleability.
3. Consensus: difficulty retarget extremes, time-warp, ticket/stamp rules, snapshot/restore.
4. Cryptography review of the transport (home-made Noise-like construction with a SHA-256 key stream). A standard library AEAD and a standard handshake would be easier to audit.
5. Fuzzing of every decoder (ops, terms, frames, snapshots).
6. The container image and Kubernetes manifests (image was not built in this sandbox; manifests were only syntax-checked).
7. Economic attacks: selfish mining, fee sniping, eclipse of a node at start-up (the seed list is trusted).

## Suggested order

Circuits for the new operations (done, round 55) → fuzzing → outside audit of consensus and the transport → launch ceremony and hardware.
