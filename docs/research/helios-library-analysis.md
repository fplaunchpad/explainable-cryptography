# Library analysis for the Helios formalisation

Source review, 10 September 2026. Recommendation: retain Mathlib for the first symbolic attack model; use VCVio as the leading candidate for subsequent computational proofs. CatCrypt-core is a credible alternative, particularly for stateful package proofs and its existing Chaum–Pedersen development. LeanDY would require substantial foundational extensions for this particular privacy property.

This assessment concerns the pinned revisions, not every branch or historical version. It is a source and dependency review, not a successful build or kernel-level proof audit. None of the three pinned toolchains is currently installed locally. The proposal's Lean/Mathlib version is 4.32.0.

| Library | Revision | Lean | Direct mathematical/framework dependencies |
| --- | --- | --- | --- |
| [LeanDY](https://github.com/SecPriv/leandy) | `e0705986c5dea547848bf80c10b5c4f88ae6868c` | 4.24.0-rc1 | Mathlib; resolved revision in its manifest |
| [VCVio](https://github.com/Verified-zkEVM/VCVio) | `6d5c7d502ad97f676293a84c3d364c518cbde117` | 4.33.1 | Mathlib 4.33.1, PolyFun, Loom2 |
| [CatCrypt-core](https://github.com/spitters/CatCrypt-core) | `91410d23b34a886fcc35765d59a93565906bbe17` | 4.30.0 | Mathlib 4.30.0, nominal-lean |

**1. The property determines the library choice.**

Cortier–Smyth prove a symbolic equivalence: an adversary cannot distinguish an election in which Alice votes X and Bob votes Y from one in which Alice votes Y and Bob votes X. The honest tally is the same. Public ballots, acceptance decisions, partial decryptions, and the final result must all be accounted for. This is stronger than checking that a designated secret term cannot be derived in one execution.

There are three distinct deliverables:

| Deliverable | Required machinery | Best starting point |
| --- | --- | --- |
| Checked replay/permutation attacks | Ballot construction, acceptance, tally algebra, explicit adversary observations | Small Mathlib-based model |
| A faithful port of the paper's positive theorem | Symbolic terms modulo homomorphic equations, adversary recipes, static equivalence, transition matching | Custom symbolic layer; none of these supplies the theorem directly |
| Computational privacy under cryptographic assumptions | Probabilistic games, adaptive adversaries, proof simulation/extraction, advantage bounds and efficiency | VCVio or CatCrypt-core |

A computational game proof is not automatically a port of the applied-pi theorem. Likewise, a finite tally example is not a proof of general privacy. These claims must remain distinct in the proposal and implementation.

**2. LeanDY: useful security infrastructure, but a poor direct fit for ballot privacy.**

The central result in [Leandy/Lib/Attacker.lean](../../external/LeanDY/Leandy/Lib/Attacker.lean) is `attacker_sound`: on a valid trace, every term in `AttackerKnows` has a public label. Its attacker can compose known terms and use the specified destructors. The surrounding library provides trace validity, protocol operations, authentication examples and automation. This is a useful foundation for proving that secret nonces or keys remain unavailable and that events have appropriate predecessors.

The fixed term language in [Core/Bytes/Types.lean](../../external/LeanDY/Leandy/Core/Bytes/Types.lean) supports signatures, hashes, symmetric and asymmetric encryption, tuples and XOR. Its asymmetric-encryption constructor has message and key arguments; it does not directly expose Helios's explicit encryption randomness, homomorphic combination, or zero-knowledge ballot proofs. Those are central to the replay variants and repair.

Candidate values are public possibilities: proving that the attacker cannot derive the constant representing X cannot express that the attacker does not know whether Alice chose X. We need an indistinguishability property about the association between a voter and a choice. I did not find an existing static-equivalence or labelled-bisimilarity development in this checkout.

Adding constructors and algebraic equations would affect normalisation, equality, typing rules, and attacker soundness. Adding a second execution and an observational-equivalence theorem is another substantial task. Reusing its DSL would not remove those obligations. I would not choose LeanDY solely because the target paper is symbolic; its existing theorem is a different kind of secrecy theorem.

**3. VCVio: strongest first candidate for the computational stage.**

VCVio represents oracle interactions explicitly, interprets them using handlers, and supplies probability semantics and relational game reasoning. That suits a voting adversary which reads published ballots and submits a ballot as a function of what it observed. The bulletin board can be a stateful handler, with the acceptance rule supplied as a parameter. Logging and sampling interpretations offer a plausible route to generating explanations from the same model, although our exact finite evaluator and its correctness connection would still need implementation.

[Examples/ElGamal/Basic.lean](../../external/VCVio/Examples/ElGamal/Basic.lean) contains an actual encryption algorithm, a correctness theorem, an explicit DDH reduction, and `elGamal_IND_CPA_le_q_mul_ddh`. Its final bound is `q * (2 * ε)` under a query bound and hypotheses bounding the associated DDH distinguishers. This is a conditional reduction; it does not establish that a particular concrete group is hard or that unrestricted adversaries are efficient.

The algebra uses standard Mathlib `Field`, `AddCommGroup` and `Module` structures. Encryption returns `(r • gen, msg + r • pk)`. For Helios, encode votes as multiples of the generator and combine ciphertexts componentwise. We must prove the homomorphic tally law and bounded decoding, including the condition preventing tally wraparound. These are additions to an existing algebraic model, rather than a new probability library.

[CryptoFoundations/SigmaProtocol.lean](../../external/VCVio/VCVio/CryptoFoundations/SigmaProtocol.lean) separates the public commitment from private prover state and provides completeness, honest-verifier zero-knowledge and special-soundness interfaces. The [FiatShamir/Sigma](../../external/VCVio/VCVio/CryptoFoundations/FiatShamir/Sigma.lean) development supplies a non-aborting signature transform, random-oracle semantics and connections to separate security files. These are useful ingredients, but a signature-unforgeability result does not by itself supply the non-malleable ballot-proof property needed for privacy. We must check the exact statement, hash inputs, context binding and extractor requirements.

I did not find a ready Helios formalisation or a dedicated Chaum–Pedersen ballot-proof implementation in the reviewed VCVio source. We would write the vote-validity relation, disjunctive proof, total-vote proof, ballot handling and privacy game. We should import the specific modules we need rather than treating the entire repository as uniformly complete.

**4. CatCrypt-core: a real alternative, with useful proof components.**

The [public release](../../external/CatCrypt-core/README.md) contains stateful probabilistic computations (`SPComp`), sub-distributions, couplings, relational Hoare logic, package interfaces, game transformations and cryptographic examples. The built-in typed heap is convenient for bulletin-board state. Its public scope is the minimal-basis release: the full concrete protocol catalogue and broader compilation/concurrent-UC developments described in the paper are not supplied here. Some basic UC-related definitions do exist in the core; the release should not be described as containing no UC material at all.

The most relevant extra asset is [Examples/ChaumPedersen.lean](../../external/CatCrypt-core/CatCryptCore/Examples/ChaumPedersen.lean): completeness, special soundness, and equality of visible real/simulated transcripts under an appropriate coupling. This is closely related to Helios's proof that two discrete logarithms agree. It still requires disjunctive composition and the appropriate non-interactive transformation before becoming a Helios ballot-validity proof.

Its commitment data internally includes the random scalar. The zero-knowledge theorem explicitly compares a projection onto visible transcript components. Any adapter must preserve that boundary; publishing the full internal tuple would expose randomness. The theorem's projection is therefore part of the specification we need to review, not an implementation detail to discard.

[Examples/ElGamalDDH.lean](../../external/CatCrypt-core/CatCryptCore/Examples/ElGamalDDH.lean) proves an advantage bound by two DDH reductions. In this particular example, messages `m0` and `m1` are parameters fixed before key generation, whereas VCVio's inspected example supports the richer adaptive/query-bounded interface. This is a statement about these examples, not a claim that CatCrypt cannot express adaptive games.

There is also integration work inside CatCrypt: the ElGamalDDH example uses `CyclicGroup`, while Chaum–Pedersen uses `GroupParam`. These custom interfaces need compatible concrete instances or a proved adapter. In `CyclicGroup`, general exponentiation is defined noncomputably through the inverse of generator exponentiation. This is adequate as abstract mathematics, but does not itself provide executable, efficient exponentiation. For our demonstrations and efficiency claims we would supply an executable implementation and prove agreement. VCVio's use of Mathlib algebra is a practical advantage here.

**5. Proof completeness and dependency findings.**

A comment-stripped textual scan of repository-local import closures found:

| Entry point | Local modules reached | Literal `sorry`, `admit`, or `axiom` hits |
| --- | ---: | ---: |
| LeanDY `Leandy.Lib.Attacker` | 25 | 0 |
| VCVio `Examples.ElGamal.Basic` | 95 | 0 |
| VCVio `VCVio.CryptoFoundations.SigmaProtocol` | 52 | 0 |
| CatCrypt `CatCryptCore.Examples.ElGamalDDH` | 16 | 0 |
| CatCrypt `CatCryptCore.Examples.ChaumPedersen` | 79 | 0 |

These counts are not kernel dependency checks: external libraries were not traversed, generated declarations were not inspected, and record hypotheses are not global axioms. They justify investigating the selected modules, not claiming that the libraries have been fully audited.

Elsewhere VCVio contains unfinished proofs, including Fiat–Shamir with abort and GPV hash-and-sign. These are not evidence that the selected ElGamal theorem depends on `sorry`. CatCrypt's Curve25519 file includes explicit assumptions for primality and basepoint facts; the selected example closures did not reach that file. CatCrypt also configures `-E hasSorry`, which rejects builds producing that Lean diagnostic.

For adoption, compile the selected entry points and run `#print axioms` on the reused and final theorems. Review explicit security hypotheses separately. A proof can use only Lean's standard axioms while assuming precisely the protocol-security property we intended to establish; an axiom list alone cannot detect that specification mistake.

No builds were attempted because the exact toolchains and dependency checkouts are not installed. This is an unperformed validation step, not an observed build failure. Test candidates in isolated Lake projects before changing this repository's toolchain. VCVio's optional native crypto backends are unnecessary for abstract Helios proofs.

**6. What we must build regardless of library.**

- Define ballot format, candidate positions, voter authentication, publication order, acceptance, rejection and tallying. The paper's formal process stops on an invalid submission; discarding it and continuing is a different model that needs its own argument.
- Keep a common adversary interface across original, whole-ballot-weeding and ciphertext-component-weeding policies. Do not ban the replay in the adversary definition; rejection must follow from the protocol's checks.
- Prove the replay and permutation witnesses with the public observations explicit. Candidate ciphertexts must remain opaque to a symbolic adversary except through the permitted operations.
- Specify the cryptographic property required of ballot proofs. Ordinary encryption privacy or proof completeness is insufficient. If the crucial property is initially assumed, label the repair theorem as conditional.
- Model the entire public view, not just the tally. Equal totals do not imply privacy if ballots or proofs reveal the votes.
- Separate fresh symbolic names from concrete random samples. Concrete ciphertext collisions have probabilities and can affect duplicate rejection; a computational proof must account for them.
- Connect executable tables to the mathematical model. A small finite example demonstrates the attack mechanism; it cannot establish computational secrecy against an unrestricted observer of a small group.

**7. Recommended implementation sequence.**

First implement the replay/permutation demonstration over Mathlib with an explicit restricted symbolic observation model. Make protocol policies and witnesses reusable. This work is useful under either future library choice and needs no toolchain migration.

For a faithful positive symbolic theorem, write the missing symbolic equivalence layer explicitly. Start with the paper's scheduling, trust and rejection assumptions, and prove the accepted-ballot characterisation before the final equivalence. This is a significant formalisation project; neither VCVio nor CatCrypt eliminates it.

For a computational development, start a separate pinned VCVio project and validate a small ballot game using its ElGamal primitives, an adversarial submission handler, and an exact replay distinguisher. Compile and audit the dependency chain. Use CatCrypt as the alternative if a corresponding prototype shows that its stateful proof rules and existing Chaum–Pedersen development reduce the total adaptation work. Do not combine both probability frameworks merely to reuse one lemma.

The decisive prototype should expose acceptance, public observations and the intended proof assumption, not just encrypt and decrypt a message. It should also connect one computed attack table to a proved probability. Success would validate the architecture; it would still leave the repaired protocol's privacy proof as the main research task.

My present ranking is VCVio first for the computational extension, CatCrypt-core second with a meaningful advantage in Chaum–Pedersen reuse, and LeanDY third for this specific task. For the immediate symbolic milestone, a focused Mathlib development remains the most direct choice. We should reuse probability, algebra and game reasoning, and spend our new proof effort on Helios and its explanations.
