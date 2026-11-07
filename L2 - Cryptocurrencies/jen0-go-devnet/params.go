// Jen-0: first experiment of Proof of Minting + mining on Bronze Jen.
//
// This file holds every consensus constant of the experiment in one place.
// SPEC references point to "Zen Protocol Specification (Draft 0.1)".
//
// Deliberate simplifications of Jen-0 (see README.md):
//   - Leaf strikes prove signatures and fee limits of 4 transfers (the part
//     that removes signatures from blocks). Balance and nonce updates are
//     executed directly by every node; proving them is Jen-1.
//   - The "stamp" is the list of leaf proofs of the block; recursive merging
//     into one proof is Jen-1.
//   - Block time is shortened from 2.5 min to TargetBlockSeconds for a
//     devnet that finishes in minutes.
package main

const (
	// Pico is the smallest unit: 1 JEN = 10^12 picograms (SPEC 2).
	Pico = uint64(1_000_000_000_000)

	// LeafSize is the number of transfers proven by one leaf strike (SPEC 4.3, Open: 4 or 8).
	LeafSize = 4

	// Fee limits for Bronze Jen (SPEC 2): fee/(amount+fee) must lie in [0.01%, 6%].
	// Expressed as integer ratios so the circuit and the nodes use identical arithmetic:
	//   fee * FeeMinDen >= amount + fee      (fee rate >= 1/10000)
	//   fee * FeeMaxDen <= FeeMaxNum * (amount + fee)   (fee rate <= 6/100)
	FeeMinDen = 10000
	FeeMaxNum = 6
	FeeMaxDen = 100

	// StandardFeeBps is Jen's standard fee, 1% = 100 basis points (purity target, SPEC 6.2).
	StandardFeeBps = 100

	// MinterSharePct of each block's fee pot goes to minters, one equal share per strike;
	// the rest goes to the sealing miner (SPEC 4.6, Open: 75/25).
	MinterSharePct = 75

	// InitialReward is the raw reward of block 1, in JEN (SPEC 5.4).
	InitialReward = 2520

	// TargetBlockSeconds: devnet block time (real Jen: 150 s).
	TargetBlockSeconds = 15

	// BlowDifficulty: a blow wins with probability 1/BlowDifficulty (SPEC 4.2).
	// Fixed for Jen-0; Jen-1 adjusts it like a difficulty.
	BlowDifficulty = 60_000

	// GenesisSealDifficulty: starting seal difficulty (expected hashes per block).
	GenesisSealDifficulty = 1_500_000

	// Genesis accounts.
	GenesisUsers       = 64
	GenesisUserBalance = 1000 * Pico
)
