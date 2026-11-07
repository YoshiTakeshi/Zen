# Zen — real proofs for the new operations: findings and plan (Justus L. Ludovic)

## Where we are (updated round 55)
All seven steps are done. Every operation (vaults, channels, orders including bids and the claim, factories; tags 1–18) is carried by the block proof: four operation leaf circuits, the universal merge, shrink, BN254 layer and Groth16 (196-byte stamp, vk 1008 bytes, files in `out_v7/`). Soundness tests (`soundness.rs`) try 583 rule-breaking witnesses without finding a circuit that proves what the node refuses.
Open before any launch: (1) the Groth16 setup is single-party, a public multi-party ceremony for this exact circuit is needed; (2) the foreign payment proof of an order claim is checked by every node, not inside the circuit; (3) fuzzing of decoders, an outside audit, and the other later items (encrypted tower storage, tower payment, wider peer discovery, splicing).
The sections below keep the original findings and plan as written at round 49; the Status list at the end is the record of what was done.

## What reading the circuit showed
1. **The circuit's hash is Poseidon; the lock rules use SHA-256.** A lock's address is `SHA-256(encode(terms))`, and the signed messages of vault claims, channel states, factory states and closes are SHA-256 too. A SHA-256 compression costs tens of thousands of gates in plonky2; a channel update would need several. Not workable. The lock address and every signed message must move to **Poseidon over field elements** (the terms laid out as a fixed list of elements, not a byte string). This is a consensus format change (testnet only, so it is cheap now and impossible later).
2. **Variable-size terms.** Factories hold up to N members, each with its own state and point locks. The circuit needs fixed maxima (members, point locks per channel) and a padded layout. Today the limits exist (`MAX_PLOCKS`) but are not tuned for a circuit.
3. **Signatures.** The existing circuit already verifies one Schnorr signature per payment (`ec::verify_sig`, the dominant cost). A channel update needs two (both parties), a factory post two, a vault claim one plus the sender's own.
4. **Moving locks.** A lock's address changes with its state, so most operations delete a leaf and insert another (two or three Merkle paths of 32 levels each, ~64 Poseidon hashes per path) besides the sender and receiver paths.
5. **Cross-chain order claims** carry a proof that a payment happened on another chain. Checking that inside a circuit means checking a proof-of-work seal of a header chain (several headers), which is by far the most expensive part. Alternative worth deciding on: orders settle in the *same* chain's coin or by a hash-time-lock (atomic swap) so no foreign header check is needed in the circuit. That changes the product (stage 6 design), so it is the owner's call.

## Plan, in order
| Stage | What | Result |
|---|---|---|
| P1 | Poseidon addresses and messages: terms as field-element lists, every signed message re-based, all tests and CLIs updated | Same behaviour, circuit-friendly format. Native tests only |
| P2 | One generic **operation slot** in the state leaf: sender touch (fee, give), lock touch (old leaf out, new leaf in), up to two payouts, selector for the op kind | Vault ops proved end to end (make, claim, refund): the smallest family, one signature |
| P3 | Channels: open, fund, update, settle, close (two signatures, point locks as a fixed-size list) | Channel ops proved |
| P4 | Factories (padded members), bids and auctions, order make/reserve/reopen/return | Rest of the ops except cross-chain claim |
| P5 | Order claim: decide the design in item 5, then prove it | All ops proved |
| P6 | Merge tree accepts both leaf kinds (payment leaf, op leaf), new shrink, new BN254 layer, **new Groth16 setup** (a ceremony for real use) | Real stamps for blocks with operations; `supports_ops() = true` |
| P7 | Soundness tests: for each op, a witness that breaks one rule must fail to prove | The review of the circuits themselves |

Cost guess (to be measured at P2): an op slot is about the size of two to three payment slots, so a block of the same size holds fewer ops than payments; block size and proving time per block (now ~minutes on the test machine) will need tuning, and the block limit `MAX_OPS` (64) may drop.

## Decisions needed from the owner
- **P1 now?** It changes every lock address and signature format. Recommended: yes, it is the prerequisite.
- **Order claims (item 5):** keep the foreign payment proof (heavy circuit) or move to a hash-lock swap (light circuit, different trust model).

## Status
- **P1 done (round 49):** Poseidon addresses and signed messages, tested.
- **P2 shape, from reading the circuit:** an operation becomes its own leaf proof of a new *family* circuit (vault ops first), same row count and gate set as the state leaf so the universal merge can take it; a block's leaves stay chained by root, so operations keep their order. The merge gets a three-way (later more) choice of leaf key. Each op leaf checks the sender's signature on the new Poseidon message, the sender's balance and nonce, the lock's address against its terms, the rule of the op, and the Merkle paths of every account the op touches; the node's replay records those touches, so the prover gets exactly the paths it needs. Measured sizes today: a state leaf of 4 payment slots is 2^13 rows with its signature-leaf check; a signature costs about 1 000 rows, a payment slot about 1 000, so an op leaf with one op is estimated at 3 000–4 000 rows. Block data hash: op leaves add their data hash in block order after the payment leaves.

- **P2 done (round 50):** vault family (Make with vault terms, VaultClaim, VaultRefund) has a real op-leaf circuit; plonky2 proofs verify and match the node's replay, data hash included. Measured about 2^11 rows. The merge now takes state leaves and op leaves. Still open: other families (P3–P5), Groth16 setup must be regenerated at P6 because the merge circuit changed.

- **P3 done (round 51):** channel family (make, fund, start, update, settle, close; streams) has a real leaf circuit with three signature slots and eight point-lock opening checks, at the common 2^13 shape. The merge now takes any number of leaf families (a flag per family on each child). Consensus tightened in three places so circuit and node agree (update number < 2^62, expiry < 2^62, a settle's witness must open its lock). Next: P4 (factories, bids and auctions, order make/reserve/reopen/return).

- **P4 done (round 52):** order leaf (make, reserve, bid, reopen, return; auctions) and factory leaf (make, fund, start, post, exit, exit-now; eight members as witness) have real circuits at the common 2^13 shape, wired into `build_family`, the merge (four op keys) and the prover. Only the order claim remains unprovable (P5). Next: P5.

- **P5 done (round 53):** the order claim is proved as far as the state goes (reservation window, payout of the whole lock to the taker, lock removed, proof digest signed and in the block data). The foreign payment proof is still checked by every node, not inside the circuit (it needs other chains' headers and a foreign block body hash). All operations are now provable. Next: P6 (merge for all leaf kinds already done; new shrink, BN254 layer, Groth16 setup, `supports_ops()`).

- **P6 done (round 54):** new shrink (2^13) and BN254 layer (2^12) over the four-key merge, new single-party Groth16 setup (4.2 M constraints, vk 1008 bytes), and Groth16 stamps carry operations of every family (test with a node holding only `zen.vk`). The setup is **not** a ceremony: a public multi-party setup for this circuit is a launch step that cannot be done here. Next: P7 (soundness tests for each operation's circuit).
- **P7 done (round 55):** `soundness.rs` runs 583 rule-breaking tries over the four leaf circuits (tampering, ±6 height scan, fee variants, family-specific rule breaks); every try the node refuses either does not prove or proves only the honest statement. A deliberately removed rule (order Reopen window) was caught by 11 tries, so the battery does detect bugs. Not covered: node-only rules (subgroup, key binding, y sign, new-address uniqueness, distinct members, foreign payment proof), far-from-edge heights, constants `ntime`/`CHAIN_ID`. Next: the later items (launch preparation including a multi-party ceremony, fuzzing, encrypted tower storage, tower payment, wider peer discovery, splicing).
