# Research idea: a Lean election framework for privacy, receipt-freeness and verifiability

Recorded 2026-09-12; scope updated 2026-09-16. **Status: staged research direction.** The transfer theorem
below is conjectured; the language and its computational semantics have not been
implemented. This note records the discussion, not an instruction to begin
development. [task list.md](../../task%20list.md) remains the only development
backlog.

## Research question and intended contribution

Can one election semantics in Lean support reusable, checked proofs of ballot
privacy, receipt-freeness and end-to-end verifiability, and expose exactly which
protocol restrictions and trust assumptions make those properties compatible?

The first direction is to reconstruct the CSF 2026 framework's shared election
model and proof transformations in Lean, extending its intended scope to
receipt-freeness and verification after tallying. This is a framework
formalization, not a project to reconstruct ProVerif's search engine or merely
check its certificates. Translation into Lean alone does not establish novelty;
necessary side conditions, reusable transformation theorems and tested extensions
are candidate contributions.

A subsequent question is whether security in the symbolic semantics transfers
to computational semantics under explicit cryptographic assumptions and
checkable restrictions. Each property needs its own transfer theorem.

The intended benefit is to establish the difficult abstraction argument once for
a supported class of elections. An instance would then supply its symbolic
security proof, admissibility proof and concrete primitive assumptions. Applying
the transfer theorem would yield a computational security theorem for that
instance. Extending the supported primitives or protocol features would require
new soundness arguments.

For a formal-verification audience, this is a semantics-preservation problem for
security properties: one protocol description has two interpretations, and the
bridge must preserve the relevant hyperproperty. Ordinary trace inclusion alone
does not establish ballot privacy, which compares observations of two elections.

## Architecture to emulate

Cheval, Cortier, Debant and Moser's ProVerif election framework provides shared
protocol infrastructure for privacy and verifiability, including unbounded
concurrent elections, voters and votes. It is a useful design reference for a
common election description and reusable proof interfaces. ProVerif reasons
symbolically about cryptographic terms and equations. The paper's framework
targets mixnet tallies and explicitly excludes homomorphic tallying (§IV-E);
its Helios-like example is not our historical component-weeding protocol.
[Framework paper](https://bblanche.gitlabpages.inria.fr/proverif/publications/ChevalCortieretalCSF26.html),
[local paper](../../_references/cheval-cortier-debant-moser-2026-privacy-verifiability-proverif.pdf).

The proposed Lean architecture has four parts:

| Part | Proposed content |
| --- | --- |
| Shared election description | Registration, distinct voting and verification credentials, voter programs and disclosures, ballot validation, board updates, trustee actions, tallying, verification before/after tallying and public outputs. |
| Symbolic interpretation | Terms, equations, fresh names, processes and explicit attacker operations and observations. |
| Computational interpretation | Encodings, randomized algorithms on bitstrings, a security parameter, stateful interaction and arbitrary probabilistic polynomial-time attackers. |
| Transfer theorems | Separate privacy, receipt-freeness and verifiability preservation claims under property-specific restrictions and primitive assumptions; computational transfer is a later research stage. |

A type system could enforce honest-program restrictions on keys, randomness,
cryptographic operations and information release. Runtime validation and its
cryptographic justification must handle adversarial inputs; typing honest
programs does not restrict attackers to honestly generated ballots.

ProVerif integration would be an optional automation interface. Relying on its
results inside a Lean theorem would require justified model/query translation
and checked evidence, or an explicitly larger trusted base. Recreating the
ProVerif engine is not the research objective.

## Receipt-freeness scope and candidate instances

Scope agreed on 2026-09-16; definitions and protocol instances remain **staged**.
Ballot privacy concerns distinguishing votes from allowed observations.
Receipt-freeness additionally concerns a voter's ability to convince an adversary
of their vote by disclosing information. It needs a separate definition, including
which secrets, randomness and messages can be disclosed, when disclosure occurs,
and which communications remain inaccessible. Stronger interactive coercion
resistance is not implied and needs a separate adversary model.

The shared semantics should represent voter identities, voting credentials and
verification trackers separately; verification can occur after tallying. Voter
strategies for presenting a plausible alternative account must be executable
within the allowed information and communication interface. A proposed strategy
must both preserve the voter's intended vote under the stated conditions and
make the relevant adversary views indistinguishable; an always-aborting strategy
is not sufficient. The exact quantifier order and admissible election contexts
remain to be specified. Proof-only extraction of credential or vote relations
must not become an operation available to the adversary.

Two candidate instances exercise different mechanisms:

| Instance | Motivation and literature boundary |
| --- | --- |
| BeleniosRF | Signatures on rerandomizable ciphertexts support server-side ballot rerandomization. The original work proposes receipt-freeness and verifiability; the CSF 2023 analysis finds verifiability attacks under particular credential/network corruption assumptions. Reproduce these as verifiability controls, not as receipt-freeness attacks. |
| SeleneRF | Combines Selene's tracker-based verification with ballot rerandomization. The CSF 2023 paper proves verifiability results and explicitly leaves the expected stronger receipt-freeness guarantee for future proof. Treat receipt-freeness as a candidate claim to prove or refute, not inherited evidence. |

Sources: [BeleniosRF, CCS 2016](https://members.loria.fr/skremer/files/spooc/publications/b2hd-CCFG-ccs16.html)
and [CSF 2023, introduction and protocol analysis](https://satoss.uni.lu/members/jun/papers/CSF23.pdf).
The [CSF 2026 framework](https://bblanche.gitlabpages.inria.fr/proverif/publications/ChevalCortieretalCSF26.html)
explicitly leaves tracker-based verification after tallying outside its current
scope (§VIII), naming Selene among the examples. Supporting SeleneRF therefore
requires extending the framework's execution/verification interface.

The smallest proposed experiment is a precise symbolic receipt-freeness definition
with an independently derived receipt-producing counterexample and a successful
restricted example with a concrete alternative-disclosure strategy. Candidate
controls also include the BeleniosRF shared-credential/dropped-ballot verifiability
attack, a tracker disclosure that reveals the vote, and adversarially constructed
accepted ballots outside honest sampling. Each control must name the property
it violates and its actual trust assumptions. Failure to find an attack proves
none of the three properties. The sole development backlog is task list.md;
this section records scope, not a second implementation schedule.

## Lessons from the 2023 and 2026 verifiability frameworks

Planning update, 2026-09-13. **Status: staged.** Development obligations and
completion evidence belong only in [task list.md](../../task%20list.md).
The concrete computational case study and publication package are now complete
under the documented external-efficiency boundary. Framework implementation
and all property-transfer theorems remain unstarted.

Baloglu, Bursuc, Mauw and Pang's *Election Verifiability in Receipt-free Voting
Protocols* (CSF 2023) provides verifiability conditions and a theorem connecting
them to a general verifiability predicate on end-to-end traces (Theorem 1).
It identifies BeleniosRF attacks involving credential assignment and network
control excluded by earlier cryptographic models. Its receipt-freeness analysis
is left for future work. This is a definition-level transfer, not a computational
soundness theorem for privacy.
[Paper, introduction, §IV and conclusion](https://satoss.uni.lu/members/jun/papers/CSF23.pdf).

The 2026 framework provides the architectural precedent: a shared election model
for symbolic privacy and verifiability, with reusable proof infrastructure and
justified transformations for ProVerif. Its homomorphic-tally limitation remains
relevant to our instance. Neither paper supplies the proposed computational
privacy bridge. The 2023 paper is a complementary definition/model reference;
the 2026 paper builds on Cheval, Cortier and Debant's distinct 2023 paper,
*Election Verifiability with ProVerif*.

For our design, distinguish three obligations:

| Obligation | Required evidence | Position |
| --- | --- | --- |
| Model alignment | Definition-backed mapping of protocol operations, corruption, scheduling, challenges and public observations; explicit restrictions or protocol changes | Scope comparison documented; common interface and correspondence unproved |
| Concrete computational secrecy | Quantitative security reduction for the selected repaired protocol and scoped game | Complete under the revised external-efficiency boundary; does not prove transfer |
| Symbolic-to-computational privacy transfer | Preservation of two-world indistinguishability under proved admissibility and primitive assumptions, applied to an aligned instance | Separate staged research obligation |

The alignment table must compare actual historical symbolic and selected
computational repairs, including proof/context binding. It must also track
identities versus credentials, leaked versus adversarially generated keys,
network message loss, revoting, rejection, trustee behavior and complete public
outputs. A different repair requires a corresponding symbolic instance or a
proved applicable relation. Merely placing two security theorems in Lean does
not connect their models.

Planned controls should exercise shared credentials, dropped ballots with
apparent successful verification, and an output that reveals the challenge vote.
The BeleniosRF attack is a verifiability/model control where its assumptions
apply, not evidence of a new attack on our scoped Helios game. Excluded scenarios
must remain visible in the scope. A proof-only credential or plaintext mapping
must not become an attacker operation; if the computational reduction needs an
efficient extractor, its existence and cost require separate justification.

Acceptance of the narrow bridge requires an actual application to the aligned
Helios instance. A generic implication whose premises assume the missing
correspondence or computational privacy does not meet that criterion.

## Candidate soundness statement

The following is a schematic conjecture, not a Lean declaration:

```text
For every election description P, concrete primitive interpretation I,
corruption policy C, and permitted public leakage policy L:

  Admissible(P, C, L)
  ∧ PrimitiveSecurity(I)
  ∧ SymbolicBallotPrivacy(Symbolic(P), C, L)
  ⇒ ComputationalBallotPrivacy(Computational(P, I), C, L).
```

The conclusion should quantify over all efficient attackers and all permitted
challenge elections, with negligible distinguishing advantage as the security
parameter grows. Election size, session count and oracle use need explicit
polynomial bounds. The two interpretations must agree on the challenge policy,
corruptions, scheduling interface, rejection behavior and permitted tally
disclosure. A quantitative reduction should expose primitive advantages and
collision or other exceptional-event bounds where possible.

`Admissible` must express independently checkable restrictions and proved
interface laws. It must not assume computational privacy, the missing
correspondence, or that all accepted ballots were honestly sampled. Whether a
useful admissible class includes the intended Helios construction is itself an
open research question. Verifiability requires its own definitions and transfer
theorem. Receipt-freeness is in the intended framework scope, but is not a
consequence of this privacy-only conjecture.

## Main obstacles and falsifiers

The central obligation is to account for arbitrary computational attackers
despite the symbolic abstraction. Relevant difficulties include byte parsing,
malformed ciphertexts, identity elements, homomorphic operations, proof reuse,
Fiat–Shamir context binding, and which proof properties justify extracting an
accepted ballot's contribution. The required zero-knowledge, extraction and
simulation assumptions must be established for the actual construction.
Honest freshness also needs a probabilistic interpretation, with collisions and
tally wraparound accounted for.

Public observations must include the specified board, proofs, credentials,
accept/reject behavior and tally. Equal tallies alone do not establish privacy.
A bridge that discards an observable distinction would preserve the wrong
property.

Devillez, Pereira and Peters' *Traceable Receipt-Free Encryption* supplies a
definition-level warning. Appendix H constructs a scheme with ballots that are
negligibly rare under honest sampling but can be deliberately generated by a
malicious voter; rerandomization leaves those ballots usable as receipts. This
exposes a gap in the earlier receipt-freeness guarantee without the additional
strong-validity requirement. This is a distinct property and setting from our
historical Helios ballot-secrecy result.
[Paper, Appendices F–H](https://eprint.iacr.org/2022/822.pdf).

For the proposed bridge, a decisive falsifier would be an admissible election
with proved symbolic privacy and a computational distinguisher, under primitives
meeting the stated assumptions. Independently derived controls should include
accepted honest ballots, known replay/proof-reuse attacks and a public-output
change that reveals a vote. A failed attack search supplies no security evidence.
The receipt-freeness example could later test whether the language distinguishes
honest sampling from adversarially chosen accepted inputs. Soundness preserves
the specified property; it does not prove that the definition captures voter
expectations.

## Concrete Helios first

The concrete Helios attack, selected repair and scoped computational secrecy
case study are complete under the revised external-efficiency boundary, alongside
the completed historical symbolic proof. The two models have separate scopes;
no correspondence or transfer theorem has been proved. The
[scope comparison](helios-scope-comparison.md) and
[closing audit](helios-computational-closing-audit.md) record the exact boundaries.
These are evidence for designing the framework, not existing receipt-freeness
or verifiability proofs for it.

The existing theorem
`ExplainableCrypto.Helios.Symbolic.Historical.General.Source.scopedVoterElection_ballot_secrecy`
proves source weak labelled bisimilarity for the repaired historical scoped
elections, including valid ground candidates and honest abstention, arbitrary
finite extra administration inputs, and documented name, nonce/parameter and
channel freshness. It uses the documented tuple-tail correction. Its
[source](../../ExplainableCrypto/Helios/Symbolic/SourceBallotSecrecy.lean) and
[completed blueprint](helios-proof-blueprint.md) supply the symbolic baseline.
Connecting a new language to that source model would require proved
correspondence; a computational interpretation is not already provided by it.

## Precedents and possible novelty

Computational soundness is an established research area. Dahl and Damgård give
a restricted two-party language with symbolic, intermediate and computational
interpretations, including homomorphic encryption and zero-knowledge proofs.
Their transfer result requires particular construction proofs, setup and
protocol restrictions. It offers a concrete design precedent, not a ready-made
election theorem.
[Universally Composable Symbolic Analysis for Two-Party Protocols based on Homomorphic Encryption](https://eprint.iacr.org/2013/296.pdf).

Owl provides another precedent: an information-flow type system with a
computational soundness argument under cryptographic assumptions. Its 2023
paper's theorem concerns its own language and typing discipline, rather than
arbitrary ProVerif models.
[Owl paper](https://www.andrew.cmu.edu/user/bparno/papers/owl.pdf).

The possible contribution is a mechanized election-specific bridge, useful
instances and explicit, tested applicability boundaries. Novelty is not yet
established. Reuse decisions should account for actual adapters and assumptions,
following the [completed reuse audit](helios-reuse-retrospective.md); this idea
does not select a computational library or change any dependency pins.

## Evidence and success criteria

| Claim | Evidence class | Artifact or required evidence | Scope |
| --- | --- | --- | --- |
| Historical symbolic baseline | Machine-checked; integrated and audited in the existing development | SourceBallotSecrecy.lean and completed blueprint linked above | Documented historical repair and freshness; no computational conclusion. |
| Shared language and two interpretations | Staged | This research idea | Proposed architecture; no implementation claimed. |
| Symbolic-to-computational privacy transfer | Conjectured | Precise semantics, admissibility conditions and a Lean proof are required | Applicability to concrete Helios remains open. |
| Concrete Helios case study | Machine-checked under the documented boundary | Closing audit and scope comparison linked above | Separate symbolic/computational models; no correspondence theorem. |
| Shared privacy, receipt-freeness and verifiability framework | Staged | Separate definitions, proved transformations and protocol instances required | Includes post-tally verification; no new security theorem claimed. |
| Receipt-freeness definition regression | Staged | A formal counterpart of the cited separating construction would be required | Literature evidence only; outside baseline ballot privacy. |

An initial framework result would establish one generic symbolic proof rule or
transformation with a small protocol instance and a counterexample to a weakened
side condition. Receipt-freeness first requires its own precise definition and
controls as described above. A second instance would test reuse; computational
transfer is a subsequent research question. None of these proposed results is
claimed checked, and none would establish deployed-system security without
implementation correspondence.
