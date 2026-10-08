# Annotated paper references

Reading guide to the papers downloaded in `_references/`. Relevance notes describe
how we use a source, not which claims we have proved. See the
[results ledger](docs/research/helios-results.md) for checked evidence,
[task list](task%20list.md) for planned work, and
[external repositories](external/README.md) for reference code and library pins.
Local PDF links require the corresponding downloads to be present.

## Helios protocol, attacks and repairs

- **Ben Adida — Helios: Web-based Open-Audit Voting (2008).**
  [PDF](_references/adida-2008-helios.pdf).
  Original system context: ballot construction, auditing and election workflow.
  Useful for explaining the protocol to readers; the later Helios 2.0 analyses
  below determine the historical attack-and-repair case study.

- **Véronique Cortier and Ben Smyth — Attacking and fixing Helios:
  An analysis of ballot secrecy (JCS 2013; local manuscript dated August 2012).**
  [PDF](_references/cortier-smyth-2013-attacking-and-fixing-helios.pdf).
  Main source for the symbolic case study: ballot replay, failed repairs,
  component weeding and an applied-pi-calculus secrecy argument. Read alongside
  our documented model scope and tuple-tail correction; a symbolic result does
  not by itself establish computational security.

- **Ben Smyth — Replay attacks that violate ballot secrecy in Helios (2012).**
  [PDF](_references/smyth-2012-replay-attacks-helios.pdf).
  Source of the known concrete neutral-ciphertext/proof-reuse attack mechanised
  in this project. Shows why concrete algebra and accepted adversarial ballots
  matter when assessing the historical repair. This attack is prior work,
  not a discovery claimed by our formalisation.

- **David Bernhard, Olivier Pereira and Bogdan Warinschi — How not to Prove
  Yourself: Pitfalls of the Fiat-Shamir Heuristic and Applications to Helios.**
  [PDF](_references/bernhard-pereira-warinschi-fiat-shamir-helios.pdf).
  Motivates the stronger concrete repair and its security argument: binding the
  statement as well as the commitment in Fiat–Shamir challenges. Useful for
  explaining proof-context mutations. Our sampler and privacy-game differences
  are recorded in the computational model documentation.

## Proof infrastructure and symbolic–computational connections

- **Devon Tuma, Quang Dao, James Waters, Alexander Hicks and Nicholas Hopper —
  VCVio: Verified Cryptography in Lean via Oracle Effects and Handlers (2026).**
  [PDF](_references/tuma-dao-waters-hicks-hopper-2026-vcvio.pdf).
  Background for our computational foundation: probabilistic oracle programs,
  stateful simulation and rewinding. The actual pinned library and imported
  declarations determine available machinery; the paper is not evidence that
  our complete reduction has polynomial runtime.

- **Stefan Dziembowski, Grzegorz Fabiański, Daniele Micciancio and Rafał Stefański —
  Computationally-Sound Symbolic Cryptography in Lean (2025).**
  [PDF](_references/dziembowski-fabianski-micciancio-stefanski-2025-symbolic-cryptography-lean.pdf).
  Precedent for a mechanised symbolic-to-computational connection and a source
  for reuse investigation. Its expression framework and assumptions do not
  directly supply soundness for our stateful homomorphic election model.
  See the [reuse exploration](docs/research/helios-reuse-source-exploration.md).

- **Vincent Cheval, Véronique Cortier, Alexandre Debant and Florian Moser —
  Simultaneously Proving Privacy and Verifiability: A ProVerif Framework for
  Internet Voting (2026).**
  [PDF](_references/cheval-cortier-debant-moser-2026-privacy-verifiability-proverif.pdf).
  Architectural reference for shared election models, reusable invariants and
  symbolic proof transformations. Its framework excludes homomorphic tallying
  and does not provide our intended computational privacy transfer. See the
  [framework design note](docs/research/election-computational-soundness-idea.md).

## Misconceptions and experiment design

- **Ben Greenman, Sam Saarinen, Tim Nelson and Shriram Krishnamurthi —
  Little Tricky Logic: Misconceptions in the Understanding of LTL (2023;
  arXiv submission 2022).**
  [PDF](_references/greenman-saarinen-nelson-krishnamurthi-2023-little-tricky-logic.pdf).
  Methodological reference for eliciting misconceptions and separating
  specification reading, specification writing and concrete-behaviour judgments.
  Its surveys, think-aloud work and response coding inform our proposed study.
  It diagnoses LTL misconceptions; it does not establish that checked
  cryptographic counterexamples improve comprehension.
