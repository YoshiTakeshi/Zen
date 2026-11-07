# Zen (Bronze Jen chain): what a block carries, and how nodes check it

Draft rule set, matched by the benchmark code (p2sigopt/src/blockdata.rs, leaf and merge circuits
in p2sigopt/src/main.rs). Author: Justus L. Ludovic.

## 1. Contents of a block

| part | size | what it is |
|---|---|---|
| version, slots per leaf, leaves | 5 B | fixed protocol shape (here 16 x 8 = 128 slots) |
| payment count per leaf | 1 B per leaf | real payments fill the first slots of a leaf |
| payments | ~12.6 B each | sender index (4 B), receiver index (4 B), amount (varint), fee (varint) |
| public values | 14 x 8 B = 112 B | root before (4), root after (4), fee total, payment count, data hash (4) |
| Groth16 proof | 196 B | BN254, verifies everything above |

Measured: block A, 128 payments: 1,632 B of payments + 112 B + 196 B = **1,940 B (~15 B per payment)**.
Block B, 77 payments: 999 B + 112 B + 196 B = 1,307 B.
No signatures are published: each one was checked inside the proof, and only the proof is needed to
trust that every payment was signed by the sender's key.

## 2. Why the payments must be published (data availability)

The proof shows that the new root is correct. But a root alone does not tell anyone their balance,
and the next prover needs the full tree to build the next block. If a prover could publish a valid
proof but keep the payments to itself, nobody else could continue the chain.

So the proof commits to the payments:
- each leaf circuit hashes its 16 slot entries `[enabled, sender, receiver, amount, fee]`
  (all zero on a padding slot, enforced) with Poseidon;
- each merge hashes the two child hashes; the stamp's last 4 public values are the result;
- the circuit forces real payments to be a prefix of each leaf (`enabled` can only go 1 -> 0),
  so the per-leaf counts are enough to rebuild the exact slot layout.

A block whose bytes do not hash to the proof's data hash is invalid, whatever its proof says.

## 3. What a node checks, in order

1. **Chain link:** `root before` == the `root after` of the block it builds on.
2. **Proof:** Groth16 verify with the 14 public values (about 2 ms; one fixed verifying key, 944 B).
3. **Decode** the bytes (version, power-of-two leaves, counts <= slots, minimal varints, no trailing bytes).
4. **Replay** the payments on its copy of the state, with the circuit's rules:
   sender and receiver exist; amount, fee < 2^62; balance >= amount + fee;
   fee >= 0.01% and <= 6% of (amount + fee); sender nonce + 1; receiver balance < 2^63.
5. **Compare** its own (root before, root after, fee total, count, data hash) with the public values.
   All five must match.

Measured: the node replay matches the proof for blocks A and B; changing one byte of the payment
data (a fee) makes the replay disagree and the block is rejected.

## 4. Replay protection (nonces)

Each account leaf is `Poseidon(pk, balance, nonce)`. The signed message is
`Poseidon(sender pk, receiver pk, amount, fee, sender nonce)`, and the circuit increments the
sender's nonce. A signed payment is therefore valid exactly once:
- in the same block, a second copy fails because the sender's leaf now holds nonce + 1
  (tested: `REPLAY=1` re-submits the first payment with its original signature: no proof);
- in a later block, the same: the leaf in the tree has moved on;
- on another fork, the chain-link rule ties each block to the exact previous root.

## 5. Padding

Blocks always have the same shape, so one Groth16 key serves every block. Unused slots have
`enabled = 0`: no state change, no fee, not counted, all-zero entry in the data hash. A padding slot
costs the same proving time as a real one, so the fees of a block must pay for its full shape.

## 6. Not covered yet

- **New accounts.** A payment's receiver must already exist. A registration operation (public key,
  32 B) that fills an empty leaf is needed, with its own slot type in the circuit.
- **Paying the prover.** The fee total is public, but no account is credited with it yet. The
  prover's account should be updated inside the circuit (so it is part of the new root).
- **Storage.** Nodes must keep and serve the payment data of past blocks (12.6 B per payment)
  so new nodes can rebuild the tree; a snapshot of the tree can replace old blocks.
- **Physical links.** Mint, redeem and peg readings (Ren, Ten, Sen) are separate operations not in
  this circuit.
