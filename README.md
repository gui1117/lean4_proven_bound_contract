# Toy project: A Smart Contract VM, with statically checked gas bound, based on λ-calculus, in Lean4

The VM language is the three form λ-calculus written with De Bruijjn indexing, with strict evaluation.

A smart contract is composed of a code, a bound on the number beta-reduction, and a proof that for any natual number as input, the code will finish in the given bound.

The gas metering proof is checked when the contract is deployed and not when the contract is executing like EVM. Executing the proof should still happen in a runtime-gas-metered environment like RISC-V.
