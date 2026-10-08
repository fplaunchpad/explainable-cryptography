# Prioritised remaining work

This is the canonical development task list. Work from the top down. Update
checkboxes only when the acceptance criteria have evidence; a proposed theorem
or successful search is not a completed proof. The current focus is the Helios
replay-and-repair case study. The finite replay/permutation milestone is checked;
see [results](docs/research/helios-results.md). The agreed order is the historical symbolic theorem first, then a concrete
cryptographic repair. The upstream library builds remain open for that second phase.

The format follows [SAL's task list](https://github.com/fplaunchpad/sal/blob/223d4976b28d7df249c6c9d91475557ff9f1d196/PRIORITIZED_REMAINING_WORK.md).
Use the [formal research workflow](docs/research/workflow.md) for claim records,
falsifiers, controls, and evidence labels.

## 0. Establish the working baseline

- [x] Prepare the standalone public research project with fresh Git history,
  an MIT license, and a proposal-free development backlog. Evidence (validated,
  8 October 2026): all Lean sources match the original working tree byte for
  byte; `lake build` succeeds (3287 jobs) under the new package name. The three
  public reference submodules retain their exact revisions and upstream licenses;
  the private research-skills submodule is omitted. CI is configured to run
  `lake build`; its hosted result is recorded separately after publication.

- [x] Organise the existing proofs under `ExplainableCrypto/`, group OTP proofs and visuals
  under `ExplainableCrypto/OneTimePad/`, and add a single `ExplainableCrypto.lean` entry point. Evidence:
  Main library renamed to `ExplainableCrypto` at the user's request;
  `lake build` passes with the original examples and Helios results under the
  new imports and namespaces.
- [x] Preserve LeanDY, VCVio and CatCrypt-core at their inspected revisions as
  submodules under `external/`. Keep them independent of the demo build.
- [x] Record the [source-level library analysis](docs/research/helios-library-analysis.md)
  at the pinned revisions. Library build validation remains
  open below; source inspection is not a successful build.

## 1. Specify the Helios experiment and resolve the repair target

- [x] **Write `docs/research/helios-model.md` before adding
  Helios proofs.** Target Helios 2.0 as described by Cortier–Smyth, rather than
  Adida's 2008 mixnet. State the ballot encoding, adversary operations, public
  observations, voter order, trusted parties, rejection semantics, and allowed
  tally disclosure. Map each choice to the paper's section or equation.
  Acceptance: a precise swapped-vote claim, a smallest falsifier, proposed Lean
  declarations, and an explicit list of abstractions and residual assumptions.
- [ ] Resolve the repair's concrete domain-check ambiguity in §4.1: the stated
  membership condition in `Z_p*` does not exclude `(1,1)`. Compare the attack,
  symbolic equations and available corrections or later specifications. Record
  unresolved details instead of silently inventing an intended repair. This
  blocks claims about the complete concrete repair, but not verbatim replay.
  **Source investigation recorded:** [repair discrepancy](docs/research/helios-repair-ambiguity.md).
  Smyth explicitly identifies the missing identity operation in the earlier
  symbolic model. No correction to the exact concrete domain condition has
  been established. **Direction agreed:** reproduce the historical symbolic
  theorem first, then address a concrete cryptographic variant. This discrepancy
  remains an open obligation of the concrete phase; it does not block faithful
  reproduction of the historical symbolic theory.
- [x] Hand-derive the three-voter fixtures for ordinary voting, verbatim replay,
  and candidate permutation. Include both swapped worlds, accepted/rejected
  outcomes and all public observations needed by the distinguisher. Acceptance:
  expected values come from the paper and arithmetic, not from evaluating the
  implementation being tested.

## 2. First checked result: the replay and failed repair

- [x] Implement a small executable model in `ExplainableCrypto/Helios/Model.lean`, using
  Mathlib and an explicit symbolic attacker interface. Separate private state
  from public observations. Do not let an adversary pattern-match on a hidden
  plaintext, and do not prohibit replay in the adversary definition.
- [x] Add PASS/FAIL Small Proof-Oriented Tests in `ExplainableCrypto/Helios/SPOT.lean`:
  ordinary valid ballots are accepted; the original policy accepts replay;
  the relevant repaired policy rejects it for reuse; an unrelated valid ballot
  remains acceptable. Include controls against universal rejection, a constant
  tally, and execution stopping before tally publication.
- [x] Prove `ExplainableCrypto/Helios/Replay.lean`: the same adversary distinguishes the
  swapped-vote worlds after copying Alice's ballot. Prove acceptance, tally
  calculation and the observation used to distinguish. State exactly whether
  the result is a symbolic counterexample or a probabilistic game theorem.
- [x] Prove `ExplainableCrypto/Helios/Permutation.lean`: rejecting identical whole ballots
  still permits the candidate-permutation witness. Check component proof
  preservation and the aggregate validity condition in the chosen model.
- [x] Exercise executable conjectures with Plausible before attempting the
  difficult general lemmas. Generate well-formed/reachable elections, run a
  known-broken control first, record seeds, sizes, counts and `gaveUp`, and keep
  a deterministic small-domain backstop. Promote decisive failures to named
  counterexample theorems; clean test runs do not establish secrecy.
- [x] Add all Helios modules to the build, inspect their public statements and
  `#print axioms`, and record results in `docs/research/helios-results.md`.
  Acceptance: checked attacks and controls, no unreported proof holes, and a
  clear separation between attack evidence and a general repair theorem.

Evidence for this section: [claim ledger and reproduction commands](docs/research/helios-results.md);
`lake build` passes (3269 jobs). All results have the finite-model scope recorded
in the specification; no complete applied-pi formalisation is claimed.

## 3. Historical symbolic repair first

- [x] Prove that ciphertext-component weeding blocks the selected witnesses
  while permitting ordinary executions under stated freshness assumptions.
  Label this as attack prevention, not general ballot secrecy. Evidence:
  `components_block_replay`, `components_block_permutation` and
  `fresh_ballots_accepted` in `ExplainableCrypto/Helios/SPOT.lean`, under the finite model's
  distinct symbolic allocation assumption.
- [x] Replace the finite recipe bound in the historical theory layer with the
  source's unbounded term signature and equational congruence E1–E9 plus AC.
  Prove substitution stability and public-recipe closure. Evidence:
  `Symbolic/Terms.lean`, `Equations.lean` and `Frames.lean` under
  `ExplainableCrypto/Helios/`.
- [x] Define static equivalence over every pair of public recipes and prove that
  public recipe postprocessing preserves it. Prove a separating algebra for E
  and controls distinguishing published zero/one while identifying equationally
  equal outputs. Check the source's aggregate-proof example and arbitrary-tail
  honest-tally symmetry. Evidence: `Symbolic/Separation.lean`, `SPOT.lean`,
  `Audit.lean` and the [symbolic record](docs/research/helios-symbolic.md).
- [x] Investigate the printed tuple-termination check, retain its counterexample,
  and apply the user-authorised [documented correction](docs/research/helios-symbolic-tuple-guard.md).
  `Ballot.lean` implements the corrected predicate; controls check valid proofs,
  acceptance, printed-check failure and continued replay exclusion.
- [x] Prove termination of the source's oriented rules modulo E0, plus existence
  of reachable equivalent irreducible terms. Validate the measure with Plausible
  first. Add a sound/complete matcher for raw root rules and controls showing
  why failed root matching does not imply irreducibility. Evidence:
  `Symbolic/Rewriting.lean`, `RootReduction.lean`, `RewriteSPOT.lean` and the
  [rewriting record](docs/research/helios-rewriting.md).
- [x] Prove the conditional termination-to-confluence framework, including
  equivalence between E-equality and joinability when local confluence holds.
  Prove the homomorphic three-ciphertext overlap unconditionally, retaining
  raw-syntax counterexamples and seeded tests. Evidence:
  [confluence record](docs/research/helios-confluence.md), `Confluence.lean` and
  `HomomorphicOverlap.lean`. The full local-confluence premise is still open.
- [ ] **NEXT — establish confluence modulo E0 or equivalent structural lemmas.**
  Termination, existence and the conditional confluence framework are checked.
  The three-ciphertext overlap is joined. Next analyse nonlinear decryption and
  proof-check overlaps, interactions with E0, and prove that the cases cover
  all competing steps. Refute candidate completion claims before general proofs. Prove the
  required constructor separation, nonce non-deducibility and projection
  analysis; do not assume the appendix's convergence claim as a Lean axiom.
- [ ] Prove the accepted-adversarial-ballot characterisation (Appendix B,
  Lemma 9), with explicit recipe restrictions and ciphertext-component checks.
- [ ] Prove static equivalence of honest ballot frames and final frames
  containing the public partial decryptions (Lemmas 10–12). Equality of tally
  terms and pointwise equality of frames are insufficient replacements.
- [ ] Define the historical process transitions and prove their matching, then
  assemble the parametrised ballot-secrecy theorem. Match the paper's ordering
  and rejection assumptions; continuing after rejection is a separate target.
- [ ] Generate an explanatory trace/table from the model and prove that every
  displayed tally or probability equals the quantity in the supporting theorem.
  Show the original, whole-ballot and component-weeding cases. Audit prose
  against the actual claim; list unresolved variants explicitly.

## 4. Validate the computational library choice

- [ ] Build the selected VCVio modules in an isolated Lake project using its
  pinned toolchain. Inspect the ElGamal and Σ-protocol declarations and their
  kernel-reported axioms; review security assumptions independently. Record
  exact commands, revisions and failures. Keep the current demo toolchain fixed.
- [ ] Build the corresponding CatCrypt-core ElGamal and Chaum–Pedersen modules
  separately. Check the visible/private transcript boundary and the adapter
  required between `CyclicGroup` and `GroupParam`. Do not infer build failures
  from missing local toolchains, or infer complete proofs from filenames.
- [ ] Compare a minimal ballot-game prototype in the two frameworks: adaptive
  ballot observation/submission, stateful acceptance, one checked distinguisher,
  and one exact computed probability connected to the semantics. Choose one
  framework based on proved interfaces and adaptation work. Record the decision
  and add only the chosen framework as a pinned Lake dependency when needed.

- [ ] For a computational extension, specify and establish the precise ballot
  proof assumptions, disjunctive proofs, Fiat–Shamir context binding and privacy
  reduction. Account for concrete collisions, tally wraparound, query bounds
  and efficiency. Keep this extension distinct from the symbolic theorem.

## 5. Follow-on work after the Helios milestone

- [ ] Revisit [mutation automation ideas](docs/mutation-testing-ideas.md): typed
  mutation syntax, witness search and proof-carrying classifications. Derive
  coverage from certificates and keep failed searches unresolved.
- [ ] Extend the foundations and TLS work only after recording the library
  decision and completed Helios scope. Keep planned deliverables distinct from the implemented theorem catalogue.
