# Lean security library source checkouts

Downloaded and inspected on 2026-09-10. These are source checkouts, not installed Lake dependencies. Builds and transitive theorem-axiom audits have not been run.

| Checkout | Upstream | Revision | Lean |
| --- | --- | --- | --- |
| LeanDY | https://github.com/SecPriv/leandy | e0705986c5dea547848bf80c10b5c4f88ae6868c | 4.24.0-rc1 |
| VCVio | https://github.com/Verified-zkEVM/VCVio | 6d5c7d502ad97f676293a84c3d364c518cbde117 | 4.33.1 |
| CatCrypt-core | https://github.com/spitters/CatCrypt-core | 91410d23b34a886fcc35765d59a93565906bbe17 | 4.30.0 |

This repository uses Lean/Mathlib 4.32.0. None of these checkouts shares that exact toolchain.

## Fit for Helios

- **LeanDY:** symbolic terms, traces, a Dolev-Yao attacker, and confidentiality typing. `Leandy/Lib/Attacker.lean` proves attacker knowledge is public in valid traces. `Leandy/Core/Bytes/Types.lean` has encryption, signatures and XOR, but no native homomorphic encryption or ballot validity proofs. I did not find the applied-pi static-equivalence/labelled-bisimilarity framework needed for a direct port of Cortier–Smyth. Extending its fixed term algebra would require revisiting the associated metatheory.
- **VCVio:** probabilistic oracle computations, simulation, relational proof rules, and concrete security reductions. `Examples/ElGamal/Basic.lean` proves correctness and a query-bounded IND-CPA-to-DDH reduction. Good candidate for computational ballot-privacy games; the election protocol, adversary restrictions, ballot proofs, and repair reduction remain our work. A text scan found unfinished proofs in other crypto modules, including Fiat–Shamir with abort and GPV hash-and-sign; no blanket completeness claim is justified.
- **CatCrypt-core:** publicly available minimal-basis release with stateful probabilistic computations, couplings, relational Hoare logic, package composition, ElGamal examples and Chaum–Pedersen examples. Its README explicitly excludes the full concrete protocol catalogue and broader compilation/UC distributions. The public checkout does not supply the full TLS implementation described in the paper. Curve25519 modules contain explicit axioms; dependencies of any theorem we reuse must be checked individually.

## Recommendation

Use Mathlib for the initial symbolic replay/permutation demonstrations, with the adversary observation model explicit. For computational security, evaluate VCVio first and CatCrypt-core as a strong alternative using a small compiling ballot-game example. Neither computational framework directly supplies Cortier–Smyth's symbolic theorem. Do not adopt all three or rebuild their probability infrastructure. Pin the selected revision and check the axioms of reused results before integrating.
