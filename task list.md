# Prioritised remaining work

This is the canonical development task list. Work from the top down. Update
checkboxes only when the acceptance criteria have evidence; a proposed theorem
or successful search is not a completed proof. The immediate documentation task
is complete: the [formal reference PDF](docs/formal-reference/main.pdf) makes the
existing development navigable before further proof development. The historical
Helios symbolic theorem and the
retrospective reuse audit are complete; see [results](docs/research/helios-results.md)
and the [reuse report](docs/research/helios-reuse-retrospective.md). Concrete
cryptographic attack, repair and scoped secrecy proofs are complete under the
revised external-efficiency boundary: **3/3 proof milestones**, with the publication
package complete. VCVio is selected and the root build shares one toolchain.
Section 4 records the exact assumptions, completed coverage and deferred C5–C8
machine-efficiency work. There is no active new proof-development goal.
The general election-language direction remains staged.

The format follows [SAL's task list](https://github.com/fplaunchpad/sal/blob/223d4976b28d7df249c6c9d91475557ff9f1d196/PRIORITIZED_REMAINING_WORK.md).
Use the [formal research workflow](docs/research/workflow.md) for claim records,
falsifiers, controls, and evidence labels.
The [symbolic proof blueprint](docs/research/helios-proof-blueprint.md) is the
maintained dependency map, not another task list. Current position: **B1–B10
complete**, ending at `scopedVoterElection_ballot_secrecy`. This is completion
of the stated historical symbolic scope, not computational security.

## Public repository migration (8 October 2026)

- [x] Import the latest research snapshot into `fplaunchpad/explainable-cryptography`
  with fresh public history and an MIT license for original code/documentation.
  Evidence (validated): all 1472 Lean files match predecessor main `db1c1c5`
  byte for byte; all six public reference gitlinks retain their pinned revisions.
  The proposal and private research-skills checkout are omitted. Historical
  commit IDs and hosted-run records refer to the predecessor's private history.
- [x] Check publication links and reference documents. Evidence (validated):
  2197 local Markdown links resolve, excluding deliberately local downloads and
  optional reference checkouts; both PDFs rebuild with identical extracted text
  and page counts (29 and 168). Only the two private-history link locations have
  changed rendered pixels; those pages were visually checked. Static document
  language, statement snippets and local-link checks pass. The eight independent
  attack, repair and reduction fixture scripts from CI pass.
- [ ] Verify the migrated Lean 4.33.1 default build and hosted CI. The local build
  is running; the completed Lean 4.32.0 check applied only to the older snapshot.

## Completed immediate priority: a formal reference PDF

- [x] **Build a self-contained mathematical reference for navigating the
  development**, following SAL's `docs/formal-reference` approach. Produce
  `docs/formal-reference/main.tex`, a readable `main.pdf`, a claim-to-source
  evidence ledger and a reproducible build/check command. Completed ahead of
  concrete computational proofs and framework generalization.

  Construct the exposition from the current Lean definitions and public theorem
  statements. Organize it by semantic dependencies: protocol and ballot data,
  cryptographic equations, source execution, attacker capabilities and public
  observations, security definitions, attacks and failed repairs, the documented
  repair, proof invariants and correspondence, and final source-level secrecy.
  Introduce notation before use; include a running election example, a reader's
  map, dependency diagrams and an index linking concepts to modules and exact
  declarations. Focus the exposition on Helios and its attack-and-repair proof.
  Treat common foundations, including applied-pi-calculus infrastructure and
  symbolic homomorphic computation, as verified libraries: give concise interface
  statements, relevant assumptions and source citations, without developing their
  internal definitions, algorithms or proofs in the PDF. State the particular
  cryptographic equations and observational interfaces used by Helios where
  needed to understand its security claim. Library verification retains its
  stated symbolic scope. Other demonstrations need at most navigation links.
  Keep proof-local machinery out of the main narrative unless needed to
  understand a substantive Helios obligation.

  State load-bearing hypotheses and distinguish definitions, sufficient proof
  techniques, completed results, checked counterexamples and conjectures.
  Preserve rejection behavior, freshness, full public observations, the
  tuple-tail correction and independently derived controls. Explain both the
  checked semantic-realization/structural-presentation counterexample and the
  private-name output-policy counterexample. Separate the finite attack models
  from the full historical source theorem. Present the computational bridge as
  future research, linked to the recorded idea, with no inferred computational
  conclusion from symbolic secrecy.

  Acceptance: audit mathematical transcriptions and prose against the source;
  resolve the declarations actually cited in the document through Lean; check
  source links, assumptions and evidence classifications; run `lake build` and
  the relevant existing audits; build and visually inspect the PDF for readable
  equations, diagrams, navigation and layout. Citation resolution is a regression
  gate, not proof of prose equivalence. Apply the pinned exploratory-research-note
  and formal-writing-audit skills, and record validation evidence here when
  complete.

  Completed 2026-09-12: [14-page PDF](docs/formal-reference/main.pdf),
  [LaTeX source](docs/formal-reference/main.tex),
  [claim ledger](docs/formal-reference/claim-ledger.md) and
  [rebuild instructions](docs/formal-reference/README.md). The PDF includes
  a reader's map, protocol/ballot definitions, attacks, correction, exact theorem
  hypotheses, dependency diagram, counterexamples and concept-to-source index.
  Common foundations are project-local verified library interfaces; their
  internal proofs are omitted. All 73 printed declarations resolve with
  standard axioms only; five typed restatements, five checker tests, 29 PDF-source
  local links and seven companion Markdown links pass. Required `lake build`
  and the existing 4,058-entry Helios claim audit pass. Final compilation has
  no warnings; all 14 rendered pages were inspected, including equations,
  theorem pagination, diagram, contents and index. Evidence is in
  `tmp/formal-reference/`. No main proof, dependency pin or cryptographic scope
  changed. Computational proof work and framework generalization remain staged.

## 0. Establish the working baseline

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
  `HomomorphicOverlap.lean`. `GlobalConfluence.lean` now supplies the full
  local-confluence premise.
- [x] Prove rigid constructor structure modulo E0 and joins for every pair of
  root-rule instances with E0-equivalent sources. Evidence:
  `BaseStructure.lean`, `RigidRootOverlap.lean`, `HomomorphicRootOverlap.lean`,
  seeded gates and controls in the [confluence record](docs/research/helios-confluence.md).
  `root_peak_joined` covers all seven rule schemata. `lake build` passes
  (3295 jobs), including the public-type and axiom audit. This establishes
  root overlap coverage, not arbitrary contextual confluence.
- [x] Prove confluence of ordinary contextual rewriting, including arbitrary
  nested and disjoint positions, with a reachable raw normalizer. Evidence:
  `RawNormalization.lean`, `RawNormalizationSPOT.lean`, seeded gates and the
  [ordinary rewriting record](docs/research/helios-confluence.md#ordinary-contextual-rewriting).
  `ordinary_rewriting_confluent` gives a literal common descendant for every
  pair of ordinary sequences. The retained raw-irreducible E0-decryption
  counterexample prevents treating this as modulo-E0 confluence.
  `lake build` passes (3298 jobs), including controls and the axiom audit.
- [x] Prove completeness of the quotient factor representation, construct
  arbitrary nonempty remainders, and join specified shared/disjoint homomorphic
  selections in larger products. Evidence: `FactorReconstruction.lean`,
  `FactorSelectionOverlap.lean`, and the [factor record](docs/research/helios-confluence.md#factor-reconstruction-and-arbitrary-remainders).
  Theorems expose actual steps and exact branch factor multisets. Controls
  retain multiplicity, reject a zero unit and wrong-key fusion, and preserve
  unrelated remainders. `lake build` passes (3301 jobs), including the audit.
- [x] Classify arbitrary size-two factor selections and join every pair of outer
  ciphertext fusion steps, including repeated factors and E0-equivalent keys.
  Evidence: `PairSelectionCases.lean`, `BagFusion.lean`, `OuterFusion.lean`,
  `OuterFusionSPOT.lean` and the [outer-fusion record](docs/research/helios-confluence.md#exhaustive-outer-fusion-joins).
  The generic rule laws are proved for E7; the final theorem requires only the
  two `OuterFusion` witnesses. The seeded selection gate, duplicate/key controls,
  and an internal key reduction outside this relation pass. `lake build` passes
  (3306 jobs), including the public-type and axiom audit.
- [x] Classify all modulo steps as outer fusion or single-factor reduction,
  and join every peak with at least one outer fusion. Evidence:
  `CiphertextStep.lean`, `FactorReduction.lean`, `MixedFusion.lean`,
  `FactorStepCoverage.lean`, `MixedFusionSPOT.lean` and the
  [mixed-fusion record](docs/research/helios-confluence.md#outer-fusion-versus-any-modulo-step).
  Ciphertext inversion handles E0-dependent component changes; factor steps
  retain the full output bag, including expansion. Seeded gates and independent
  key/nonce/plaintext/remainder controls pass. `lake build` passes (3312 jobs),
  including the public-type and axiom audit.
- [x] Join disjoint factor reductions with arbitrary expanding outputs and reduce
  the remaining local-confluence obligation to singleton-factor sources.
  Evidence: `FactorPeak.lean`, `CiphertextLocalConfluence.lean`,
  `FactorPeakSPOT.lean` and the [factor-peak record](docs/research/helios-confluence.md#factor-reduction-peaks-and-the-singleton-obligation).
  The same-factor case retains an explicit local-confluence premise; the checked
  equivalence does not prove that premise. Ciphertext local confluence follows
  from explicit component hypotheses. Seeded decomposition gates and fixed
  projection/component endpoints pass. `lake build` passes (3316 jobs), including
  the public-type and axiom audit.
- [x] Classify unary and non-AC binary steps across E0 representatives, join
  projection root/internal peaks, and prove unary and passive-binary local
  confluence from explicit argument hypotheses. Establish atomic irreducibility.
  Evidence: `RigidStepCases.lean`, `UnaryLocalConfluence.lean`,
  `AtomIrreducibility.lean`, `UnaryLocalSPOT.lean` and the
  [constructor record](docs/research/helios-confluence.md#unary-and-passive-rigid-binary-constructors).
  Nontrivial instantiated projection/partial-decryption peaks, ordered-member
  controls and seeded gates pass. `lake build` passes (3321 jobs), including the
  public-type and axiom audit. Arbitrary component hypotheses remain open.
- [x] Join every E5/E6 decryption root/internal peak, including all repeated
  keys and ciphertext copies, and derive decryption local confluence from its
  two argument hypotheses. Evidence: `DecryptionOverlap.lean`,
  `DecryptionLocalConfluence.lean`, `DecryptionSPOT.lean` and the
  [decryption record](docs/research/helios-confluence.md#active-decryption-rootinternal-peaks).
  The gate and controls cover E5's four and E6's seven change locations, E0-only
  matching, all key copies and fixed updated-plaintext endpoints. `lake build`
  passes (3325 jobs), including the public-type and axiom audit. The component
  hypotheses are still explicit.
- [x] Classify proof-construction and checking steps, join all E8/E9 root/internal
  peaks, and derive both constructor implications from component hypotheses.
  Evidence: `ProofStepCases.lean`, `TernaryStepCases.lean`,
  `ProofCheckingOverlap.lean`, `ProofCheckingLocalConfluence.lean`,
  `ProofCheckingSPOT.lean` and the [checking record](docs/research/helios-confluence.md#proof-construction-and-checking).
  Every step from a source with an actual E8/E9 root witness still reduces to
  ok, giving local confluence there without component hypotheses. Controls cover
  all four key and three nonce occurrences, both bits, E0 vote representatives,
  binding failures and arbitrary proof-component peaks. `lake build` passes
  (3331 jobs), including the public-type and axiom audit.
- [x] Reconstruct nonce-composition factor bags, classify all modulo steps as
  composition-factor replacements, and join their disjoint cases. Evidence:
  `ComposeFactors.lean`, `ComposeReduction.lean`, `ComposeLocalConfluence.lean`,
  `ComposeFactorSPOT.lean` and the [composition record](docs/research/helios-confluence.md#nonce-composition-factors).
  Same-factor joins retain an explicit factor-local premise. Controls preserve
  expanding outputs, multiplicity, E0 representatives, empty remainders and the
  distinction from multiplication; a nontrivial source instantiates local
  confluence. `lake build` passes (3336 jobs), including the gate and axiom audit.
- [x] Characterize E0 addition by exact non-numeric atom multiplicities and
  optional numeric counts: `baseEq_iff_addSummary` and representative lemmas in
  `AdditionReconstruction.lean` and `AdditionRepresentatives.lean`. Absence and
  a present zero remain distinct; numeric representatives retain repeated ones.
  Abstract summary reconstruction requires valid atom representatives and a
  nonempty summary. Seeded algebra/token gates and checked positive/negative
  controls pass; `lake build` passes (3342 jobs), including 445 axiom reports.
  See the [addition record](docs/research/helios-confluence.md#addition-summaries).
- [x] Classify every modulo step as an outer addition-atom replacement and join
  disjoint replacements with exact output summaries. `AdditionReduction.lean`,
  `AdditionSelection.lean` and `AdditionLocalConfluence.lean` retain an explicit
  factor-local premise for same-class peaks. Numeric-only terms are irreducible.
  Controls include changing numeric presence, two routes to an exact endpoint,
  retained names/zero, expanding outputs and a nontrivial locally confluent
  source. The seeded replacement gate and numeric-cancellation counterexample
  pass; `lake build` passes (3347 jobs), including 470 axiom reports. See the
  [addition replacement record](docs/research/helios-confluence.md#addition-replacement-joins).
- [x] Establish confluence modulo E0. `GlobalConfluence.lean` proves local
  confluence by simultaneous structural induction with locally confluent factor
  representatives; all component and factor-local hypotheses are discharged.
  Checked termination gives `confluence_modulo`, unique irreducible descendants
  modulo E0, `eqE_iff_join` and `irreducible_eqE_iff_base`. Seeded inheritance
  gates and independent mixed-constructor/negative controls pass. `lake build`
  passes (3350 jobs), including 484 axiom reports and no custom axioms. See the
  [global proof record](docs/research/helios-confluence.md#global-confluence).
- [x] Prove full-E component equality and separation for ciphertexts, proofs,
  pairing and partial-decryption construction on arbitrary inputs.
  `PassiveReduction.lean` preserves ordered component paths; `FullStructure.lean`
  uses confluence to derive the equality theorems and irreducible-target shape
  corollaries. Controls retain reducible inputs, message/binding mismatches,
  argument order and the necessity of target irreducibility. `lake build` passes
  (3354 jobs), including seeded gates and 511 axiom reports. See the
  [full-E structure record](docs/research/helios-full-structure.md).
- [x] Prove public-key full-E injectivity and exhaustive projection paths.
  `ProjectionPaths.lean` preserves pk arguments and shows that a projection
  E-equal to a ciphertext has an argument reducible to a pair, with the selected
  member E-equal to that ciphertext. Initial literal pair shape is not required.
  Controls retain nested pair revelation, both outputs, stuck names, reducible
  keys and distinct keys. `lake build` passes (3357 jobs), including seeded gates
  and 527 axiom reports. See the [path record](docs/research/helios-full-structure.md#public-key-and-projection-paths).
- [x] Prove individual restricted-name non-deducibility for all public recipes
  over protected frames. `NonceNonDeducibility.lean` combines E0 preservation,
  forward contextual protection and confluence. The theorem retains explicit
  handle-protection, public-recipe and restricted-name premises. Controls expose
  a key/ciphertext/proof/tuple, permit public projection and bit decryption, and
  refute plaintext protection and reverse-E invariance. `lake build` passes
  (3361 jobs), including three seeded gates, controls and 545 axiom reports. See
  the [nonce record](docs/research/helios-nonce-nondeducibility.md).
- [x] Exclude composed-nonce targets containing any restricted-name factor.
  `ComposedNonce.lean` proves name-factor persistence under arbitrary modulo paths
  and combines it with protection and confluence. All public recipes over
  protected frames are covered, including arbitrary reducible target remainders.
  Controls retain repeated/permuted factors, expanding remainders, and public
  ciphertexts containing protected randomness. `lake build` passes (3364 jobs),
  including seeded gates and 558 axiom reports. See the
  [composition exclusion record](docs/research/helios-nonce-nondeducibility.md#compositions-containing-restricted-names).
- [x] Instantiate the parametrized initial historical frame for both swapped
  assignments and any positive candidate count. `HistoricalFrames.lean` preserves
  exact field order and nonempty aggregates. `HistoricalFrameProtection.lean`
  proves protection and non-deducibility with separate full-frame and nonce-only
  recipe policies; the latter matches Lemma 9's explicit restriction. Controls
  check fresh literal names, aggregate fields, swaps, public handles and the
  one-candidate accepted boundary. `lake build` passes (3368 jobs), including
  seeded gates and 584 axiom reports. See the
  [historical-frame record](docs/research/helios-historical-frames.md).
- [x] Prove general honest-ballot proof validity and corrected acceptance.
  `HistoricalAggregation.lean` establishes the homomorphic fold and exact one-hot
  vote sum; `HistoricalValidity.lean` connects all field projections and proof
  checks. Empty-board acceptance holds for every positive count and chosen index;
  second-voter acceptance retains freshness and distinct-voter premises. Replay,
  nonce collision and two-one-collapse controls remain rejected. `lake build`
  passes (3372 jobs), including seeded gates and 603 axiom reports. See the
  [validity record](docs/research/helios-historical-frames.md#general-honest-ballot-validity).
- [x] Establish minimum public-recipe existence and contextual replacement facts.
  `MinimalRecipes.lean` retains the substitution, handle type and name policy;
  minimum recipes have minimum subterms and no ordinary rewrite steps. E5–E7
  cancellation applies when matching appears only after substitution. Controls
  include a two-node minimum, forbidden names, a minimum handle with a reducible
  value and a raw-normal nonminimum decrypt. `lake build` passes (3375 jobs),
  with seeded gates and 629 nonempty axiom reports plus 14 axiom-free reports.
  See the [minimum-recipe record](docs/research/helios-minimal-recipes.md).
- [x] Check the indexed-projection exception against binary tuple selectors.
  `SmallRecipeBounds.lean` excludes every size-one/two competitor under explicit
  full-E handle premises. `HistoricalSelectorSPOT.lean` proves first- and
  second-field minima of two and three nodes in the fresh historical fixture.
  The second is fst(snd(y1)); it refutes a single-binary-selector translation
  while satisfying the source's indexed exception. Normal-form and premise
  controls pass. `lake build` passes (3378 jobs), with 646 nonempty axiom reports
  plus 14 axiom-free reports. See the
  [selector record](docs/research/helios-minimal-recipes.md#indexed-tuple-selectors-and-minimum-size).
- [x] Classify arbitrary decryption paths and prove minimum-recipe head retention
  for explicit ciphertext arguments and honest-component ciphertext values.
  `DecryptionPaths.lean` retains delayed E5/E6 matching and actual argument paths;
  `MinimalDecryption.lean` and `HistoricalMinimalDecryption.lean` establish normal
  shape and normal-form composition modulo E0, with minimum, value and normality
  premises explicit. Both historical worlds and all candidate counts are covered
  under the nonce-only policy. Delayed-match, nonminimum successful decryption,
  non-normal wrapper and six-node minimum controls pass. `lake build` passes
  (3383 jobs), with 681 nonempty axiom reports and 14 axiom-free reports. See the
  [decryption record](docs/research/helios-minimal-recipes.md#decryption-with-explicit-or-honest-component-ciphertext-values).
- [x] Reconstruct strictly smaller public plaintext recipes for certified
  ciphertext products and prove the corresponding minimum-decryption clause.
  `CiphertextProducts.lean` preserves common-key agreement and repeated factors;
  `HistoricalCiphertextProducts.lean` proves the general historical size bound
  and supplies honest-component/indexed-projection leaves for every count and
  swap. The normal-form theorem retains its factor-origin certificate. Mixed,
  duplicate, wrong-key, published-handle and successful nonminimum-decryption
  controls pass. `lake build` passes (3387 jobs), with 706 nonempty axiom reports
  and 14 axiom-free reports. See the
  [product record](docs/research/helios-minimal-recipes.md#public-plaintext-reconstruction-for-ciphertext-products).
- [x] Prove full-E multiplication inversion and normal output-head restrictions.
  `CiphertextFactorValues.lean` propagates common-key ciphertext values backward
  through arbitrary factor expansion/fusion. `MultiplicationInversion.lean`
  derives both operand values and exact nonce/message equations with no normality
  premise. `MultiplicationHeads.lean` excludes passive and atomic outputs and
  gives mul/penc shape for normal representatives. Expanding-factor, E0-key,
  duplicate, unrelated-factor, zero-unit and target-normality controls pass.
  `lake build` passes (3392 jobs), with 746 nonempty axiom reports and 14 axiom-free
  reports. See the [multiplication record](docs/research/helios-full-structure.md#full-e-multiplication-inversion-and-output-heads).
- [x] Prove addition/composition path heads and full-E constructor exclusions.
  `CompositionHeads.lean` retains compose shape through nondecreasing factor
  counts. `AdditionHeads.lean` allows precisely add/zero/one endpoint shapes,
  preserving numeric presence. `ArithmeticSeparation.lean` excludes ciphertext,
  passive, named and variable outputs, restricts constants to addition's zero/one
  cases, and distinguishes add, compose and mul.
  Expansion, numeric-collapse, zero-unit, reducible-target and normality controls
  pass. `lake build` passes (3397 jobs), with 783 nonempty axiom reports and 14
  axiom-free reports. See the [arithmetic record](docs/research/helios-full-structure.md#addition-and-composition-output-heads).
- [x] Classify proof-checking paths and close the minimum checking recipe case.
  `ProofCheckPaths.lean` proves full-E success iff reachable E8/E9 matching and
  exposes the common nonce, bit and complete ciphertext binding. Minimum public
  checks cannot equal the smaller constant ok; `MinimalProofChecking.lean`
  proves normal-form composition for arbitrary substitutions/policies. Passive
  output exclusions, delayed/E0-only success, bit/binding rejection and a
  four-node minimum with reducible handles are checked. `lake build` passes
  (3402 jobs), with 824 nonempty axiom reports and 14 axiom-free reports. See the
  [checking record](docs/research/helios-minimal-recipes.md#minimum-proof-checking-recipes).
- [x] Classify arbitrary fst/snd chains and encoded historical tuple tails.
  `TupleProjectionChains.lean` proves exact bounded pair-tail and ciphertext/proof
  selector origins under explicit tuple/non-pair-field premises.
  `HistoricalProjectionChains.lean` discharges those premises, restricts all
  historical field positions and constructs product leaves for ciphertext-valued
  chains over all three handles. Both worlds/all positive counts are covered.
  Tail, reducible-field, minimum-selector, swapped-value, out-of-range and missing-
  premise controls pass. `lake build` passes (3408 jobs), with 861 nonempty axiom
  reports and 17 axiom-free reports. See the [chain record](docs/research/helios-minimal-recipes.md#projection-chain-and-tuple-tail-origins).
- [x] Prove minimum-recipe structure used by Lemma 9.
  `HistoricalMinimumOrigins.lean` completes the simultaneous pair-origin and
  ciphertext-certificate induction for the actual initial frame. Certificates
  now follow from minimum public size and retain exact target values;
  `HistoricalCiphertextForms.lean` gives constructed/honest-selector/product
  syntax. `HistoricalMinimumDestructors.lean` proves arbitrary minimum-decryption
  normal-form composition and the bounded honest-tail exception for projections.
  `HistoricalMinimumProofs.lean` classifies constructed and honest proof origins.
  All name-policy and representative-normality premises remain explicit; both
  worlds and all positive candidate counts are covered. Smaller-competitor,
  mixed/repeated-value, minimum-selector, frame and nonminimum controls pass.
  `lake build` passes (3416 jobs), with 904 nonempty axiom reports and 17 axiom-free
  reports. See the [origin record](docs/research/helios-minimal-recipes.md#minimum-historical-origins-and-destructor-composition).
- [x] Prove the accepted-adversarial-ballot characterisation (Appendix B,
  Lemma 9), with the authorised tail-guard correction.
  `Historical.General.accepted_ballot_constructor_recipe` covers every positive
  candidate count, both swaps and all valid ground candidate substitutions,
  including honest abstention and arbitrary E-equivalent representatives. Its
  public conclusion constructs an explicit ciphertext tuple with nonce-public
  recipes and literal bits satisfying the candidate sum before substitution.
  Acceptance, recipe restrictions and both honest board members are explicit.
  General minimum proof origins and borrowed-aggregate exclusion supply the
  public nonces; protection is transported through E-equal bit representatives.
  Retain raw-normalization, factor-weight, indexed-selector and missing-premise
  counterexamples: minimum recipes need not have irreducible substituted values.
  Abstention, nonliteral representations, fresh reconstruction and borrowed-proof
  controls pass. `lake build` passes (3441 jobs), including 76 new theorem audits
  and three seeded gates. See the [full candidate-substitution record](docs/research/helios-candidate-substitutions.md).
- [x] **Prove final-frame static equivalence**, including the public partial
  decryptions (Lemmas 11–12 / B8). `accepted_final_staticEq` and
  `accepted_partial_staticEq` now discharge the full all-public-recipe targets.
  Freshness, valid candidates, public submissions and sequential acceptance are
  explicit; no local-transport, binding or static-equivalence callback remains.
  All twelve local cases close. See the
  [published equivalence proof](docs/research/helios-published-static-equivalence.md).
  B1–B10 are now complete. The progress paragraphs below are historical checkpoints;
  their earlier unchecked status and open B8 cases are superseded here. Use `Historical.General.frame`
  with all valid ground candidate substitutions, `Names.Fresh`, and the full
  restricted-name policy. Equality of tally terms and
  pointwise equality of frames are insufficient replacements.
  Progress: caller-policy-preserving reconstruction now supports the full
  restricted-name policy. Static equivalence conditionally transfers acceptance
  over a common public board and supplies one shared constructor/bit witness.
  The earlier all-recipe candidate reduction to literal bit vectors is now
  superseded by the unconditional initial-frame theorem below. Freshness and key-policy distinguishers, nonempty-board
  reconstruction/replay controls and a bounded raw-observation gate pass.
  The paper's E0 reflection to open vote variables fails on a checked public
  zero-padding example; it does not refute the privacy theorem. Exact numeric-
  offset equality now handles this case, including reducible payloads. Fresh
  nonce multiplicities characterize full-E equality of arbitrary nonempty
  honest ciphertext products, and fixed-payload comparisons tolerate a changed
  honest numeric sum. Mixed public/honest ciphertext equality now reduces to
  the honest occurrence bag and strictly smaller public nonce and zero-padded
  payload observations. Protected E-values suffice even for raw-unsafe inputs;
  an entirely public nonce constructor cannot match a mixed value. Every
  ciphertext-valued minimum recipe now has a constructed/honest assembly whose
  arbitrary products group into public-only, honest-only or mixed contributions.
  Full-E inversion derives leaf key agreement; publicness, target components
  and observation bounds refer to the original recipe. The full grouped
  equality matrix and recursive key-coherence transfer now prove the ciphertext-
  valued minimum-recipe induction branch from strictly smaller public equality
  tests. Second-world coherence and minimum-syntax preservation are not assumed.
  The proof-valued branch now also transfers from smaller tests, retaining all
  four constructed-proof arguments and the one-candidate component/aggregate
  coincidence. Fresh honest proof equality follows nonce provenance. The public-
  key-valued branch now derives exact constructor/election-handle origins and
  transfers their equality tests under the full secret-name policy, including
  explicit projection/decryption paths and nonminimum-wrapper controls. The
  initial-frame partial-decryption-valued branch now derives explicit constructor
  syntax and transfers both ordered component tests. Controls establish exact
  three-node minima and show why publishing partial decryptions needs additional
  origin cases. The pair-valued branch now derives constructed/nonempty-tail
  forms, identifies equal tails by suffix length and fresh aggregate nonces,
  and transfers all comparisons involving constructed pairs through smaller
  tests against both projections. Empty-tail, colliding-nonce, truncation and
  one-candidate repeated-field controls pass. The atomic branch now proves exact
  name deducibility under the caller's policy and forces minimum recipes for
  names/constants to be literal atoms. Their exact values survive any destination
  frame without a smaller-test or freshness premise. Nonminimum sums, proof
  checks, empty tails and name wrappers remain explicit controls. Successful
  minimum projections now have exact honest field/nonempty-tail syntax and
  still reach argument pairs in either world. The stuck-check-valued branch
  derives explicit origins and preserves failure using smaller whole-check/ok
  probes before comparing all three arguments. Destination failure or minimum
  size is not assumed. Stuck projection/decryption values now force exact
  minimum recipe heads. Full-E injectivity preserves the projection selector
  and both ordered decryption arguments, and smaller argument tests transfer
  source equalities forward without destination stuckness premises. For minimum
  decryptions with partial-decryption-valued first arguments and ciphertext-
  valued second arguments, three public probes now derive destination failure
  and transfer equality in both directions. They retain structured-key E5 and
  complete E6 binding; assembly syntax and destination coherence are derived.
  Simultaneous pair/ciphertext/partial value-shape reflection now discharges
  all decryption argument-shape premises. Every source minimum decryption stays
  unmatched, and minimum non-pair arguments cannot acquire pair values. The
  complete stuck-decryption and stuck-projection minimum equality branches now
  transfer both ways without destination failure or minimum-size premises.
  The composition-valued branch now derives exact compose syntax and semantic
  indivisibility of raw leaves in both worlds. Full-E factor bags retain
  multiplicity, and strictly smaller public leaf tests transfer their equality
  in both directions. The addition-valued branch now retains optional numeric
  presence/count and atom multiplicity. Exact addition/zero/one origins derive
  both worlds' semantic atom conditions, and smaller leaf comparisons transfer
  equality, including literal numeric minima with addition E-values.
  The non-ciphertext multiplication branch now retains all internal ciphertext
  fusions. Both worlds' normal partitions derive smaller public group recipes
  with exact source factors and original size budgets. Their equality transfers
  and reassembles the original products without destination minimum premises.
  The generic arbitrary-recipe induction now follows from shared minimum
  representatives in both worlds and an assembled minimum-pair observation
  step. Structural induction reduces shared minimization to local roots with
  minimum children. Complete common-normal-value case analysis now assembles
  forward minimum equality preservation. Reverse shared minimization supplies
  destination minima and the complete reverse step. Initial-frame static
  equivalence is exactly shared minimization in both directions; local root
  transport with minimum children in both orientations suffices. Minimum-parent
  closure now solves constructed keys, partial constructors, proofs and
  semantically stuck destructors. They need no observation-preservation premise.
  The remaining interface covers only nonminimum roots with minimum children:
  successful destructors, pairs, ciphertext constructors and arithmetic, in
  both orientations. The projection cases are discharged below. See the
  [local-root record](docs/research/helios-local-root-transport.md).
  All local fst/snd cases now have shared minima when their children are
  minimum. Exact honest ciphertext-selector origins and minima close every
  nonempty ballot-tail minimum. Empty tails use bottom; one-candidate aggregate
  fields use the shorter component representative. The reduced obligation
  originally retained successful decryption/checking, pairing, ciphertext
  construction and arithmetic in both orientations. See the
  [complete projection record](docs/research/helios-complete-projections.md).
  Its full `lake build` passes (3546 jobs), with eighteen new theorem audits,
  eight controls, and the ciphertext singleton/selector/tail gate in both swaps.
  Pairing now also has shared minima for minimum children. Exact nonempty-tail
  origins and honest-field/tail matching transport supply the same shorter
  tail representative in both worlds. At this stage the remaining local cases
  are successful decryption/checking, ciphertext construction and arithmetic.
  See the
  [pair transport record](docs/research/helios-pair-transport.md).
  Its full `lake build` passes (3551 jobs), with sixteen new theorem audits,
  seven controls and the canonical tail-reconstruction gate in both swaps.
  Ciphertext construction now also closes: penc with minimum children is
  minimum in the actual initial frame, with no freshness or observation premise.
  A public nonce excludes honest/mixed groups; the selected key and grouped
  component budget fit the original assembly size. At this stage successful
  decryption/checking and arithmetic remain. See the
  [ciphertext constructor record](docs/research/helios-ciphertext-constructor-minima.md).
  Its full `lake build` passes (3555 jobs), with twelve new theorem audits,
  seven controls and the selected-key/grouping budget gate in both swaps.
  Composition now also preserves minimum size for minimum children, under
  any caller name policy in the initial frame. Equal semantic factor bags
  preserve minimum leaf costs and exact occurrence counts. The four remaining
  local cases at that checkpoint were successful decryption, successful proof
  checking, addition and multiplication; addition is discharged below. See the
  [composition minimum record](docs/research/helios-composition-minima.md).
  Its full `lake build` passes (3560 jobs), with sixteen new theorem audits,
  seven controls and the composition leaf-cost/permutation gate in both swaps.
  Addition now also closes: a public raw-E0 representative attains the exact
  atom/numeric cost and is globally source-minimum. Raw E0 equality makes it
  shared in every destination frame. The source cost theorem accepts any caller
  policy, without freshness or observation assumptions. See the
  [addition minimum record](docs/research/helios-addition-minima.md).
  The full build passes with 3566 jobs, thirty new theorem audits, eight SPOTs
  and seven definition checks. The gate detects both numeric-law defects and
  passes three seeds plus 2048 inputs. Blueprint B7-A is complete; current
  position is B7-M. Nine of twelve operator cases are closed. Successful
  decryption/checking and multiplication remain unproved in both orientations;
  final transcript equivalence and the process/secrecy theorem also remain open.
  Within B7-M, the [normal-partition minimum criterion](docs/research/helios-multiplication-minima.md)
  now proves global source minimum size from minimum pieces and an irreducible
  endpoint. It closes products of two minimum groups with a normal product of
  single-factor values. Source partitions cover either swap and any caller
  policy, without an observation premise. The full build passes with 3570 jobs,
  thirteen new theorem audits, seven controls and two definition checks. The
  gate detects duplicate-cost and unfused-endpoint defects and passes three
  seeds plus 2048 deterministic inputs. Arbitrary fused-group shared minima
  and reassembly remain open; multiplication is still an unchecked operator
  obligation, and the total remains nine of twelve closed cases.
  [Shared-piece reassembly](docs/research/helios-multiplication-reassembly.md)
  now closes B7-M step 4: it preserves both frame values and proves global
  source minimum size using exact new partition costs. Well-founded size
  induction discharges non-ciphertext products; child minimization cannot
  increase the original parent budget. That increment’s remaining interface was
  `DecryptCheckCipherMulTransport`: successful decryption/checking and
  whole-ciphertext products in both directions remain unproved. Its full
  build passes with 3576 jobs, sixteen new theorem audits, eight controls and
  three definition checks; the corrected E0-summary gate passes three seeds
  plus 2048 deterministic inputs. B7-M and the secrecy task remain unchecked.
  [Honest-only ciphertext products](docs/research/helios-honest-product-minima.md)
  are now globally minimum for all positive candidate counts, both swaps and
  valid ground votes. Every minimum equivalent has the same indexed occurrence
  bag and exact cost. Nonminimum remaining products therefore have constructed
  or mixed public groups. The full build passes with 3579 jobs, fifteen new
  theorem audits, seven controls and one definition check. The gate preserves
  freshness/multiplicity defects and passes three seeds plus 2048 inputs.
  At that checkpoint, constructed and mixed groups remained open at B7-M;
  no additional operator or top-level milestone was marked complete.
  [Constructed-only compression](docs/research/helios-constructed-compression.md)
  now proves strict cost reduction, minimum constructor origins and conditional
  shared transport. Its smaller observations and shared minima were explicit
  premises at that checkpoint. The full build passes with 3582 jobs,
  fourteen new theorem audits, seven controls and two definition checks.
  The gate detects wrong-key/singleton defects and passes three seeds plus
  2048 inputs. This increment leaves the static-equivalence task unchecked.
  [Simultaneous minimum transport](docs/research/helios-joint-minimum-transport.md)
  now derives bounded observations from two-way minima at the same bound and
  supplies both strict smaller hypotheses by unbounded recipe induction.
  Constructed-only products are discharged in the reduced criterion; the
  interface at that checkpoint was `Historical.General.DecryptCheckMixedMulTransport`.
  Mixed ciphertext products and successful decryption/checking remained open.
  The full build passes with 3587 jobs, sixteen new theorem audits, eight
  controls and five definition checks. The gate detects three known defects
  and passes three seeds plus all 4096 finite models at six bounds (7872
  premise-satisfying instances). B7-M remains current, with nine of twelve
  operators and six of ten milestones closed; this task remains unchecked.
  [Mixed compression](docs/research/helios-mixed-compression.md) now discharges
  two or more public constructors using exact indexed occurrence costs and
  the simultaneous smaller-minimum hypotheses. Every minimum mixed assembly
  has one public constructor and an equally small grouped representative.
  Minimum public nonces with one-node payloads attain global mixed minima.
  That checkpoint used `Historical.General.DecryptCheckSingleMixedTransport`:
  one-constructor mixed products and successful decryption/checking remained.
  A checked nine-to-seven-node example with minimum children keeps arbitrary
  zero-padded payload minimization explicit. The full build passes with 3592
  jobs, twenty-two new theorem audits, eight controls and four definition
  checks. The gate detects singleton/index-cost defects and passes three seeds
  plus 2048 inputs. B7-M remains current; no operator or top-level milestone
  is promoted, and this task remains unchecked.
  [Padded payload minima](docs/research/helios-padded-payload-minima.md) now
  close B7-M. Exact padded costs preserve all atoms and ones, and compare
  against every public competitor. Minimum multiplication leaves supply the
  sole constructor's minimum components; minimum nonce and padded-minimum
  payload give a global mixed minimum. Both frame values are preserved.
  `minimum_children_mul_shared_of_two_way_minima` covers all multiplication
  classes. The current interface is `Frame.DecryptCheckTransport`, retaining
  only successful decryption/checking in both directions under simultaneous
  strict smaller-minimum hypotheses. The full build passes with 3598 jobs,
  twenty-three new theorem audits, eight controls and four definition checks.
  The gate detects three known defects and passes three seeds plus 2048 inputs.
  The blueprint moves to B7-C (B7-D also open): ten of twelve operators and
  six of ten milestones are closed. Initial static equivalence and this task
  remain unchecked; multiplication itself is discharged.
  [Successful proof checks](docs/research/helios-successful-checks.md) now
  close B7-C. Four smaller public comparisons handle constructed proofs;
  minimum honest-combination origins transfer borrowed ciphertext bindings
  through raw E0 equality without an oversized aggregate comparison.
  The full operator theorem covers successful and stuck checks in the
  simultaneous induction. `Frame.SuccessfulDecryptionTransport` is the current
  interface, with both successful-decryption instances still unproved.
  Full `lake build`: 3604 jobs, twenty-two new theorem audits, ten controls
  and three definition checks; the gate catches three defects and passes
  three seeds plus 2048 inputs. The blueprint moves to B7-D: eleven of twelve
  operators, six of ten milestones. Initial static equivalence and this task
  remain unchecked at that checkpoint.
  [Initial-frame static equivalence](docs/research/helios-initial-static-equivalence.md)
  now closes B7-D and B7. Successful minimum-child decryption must consume a
  raw constructed ciphertext; full-policy secret non-deducibility excludes
  honest/mixed groups. Smaller E5/E6 comparisons transfer success and share
  the actual minimum plaintext recipe. `Historical.General.initial_frame_staticEq`
  covers every public recipe pair and valid ground candidate substitution,
  with no remaining observation/shared-minimum assumptions. Full `lake build`:
  3607 jobs, thirteen new theorem audits and eight controls; the gate catches
  both E5/binding defects and passes three seeds plus 2048 inputs. The checked
  secret-policy counterexample distinguishes zero from one if the election
  secret is exposed. B7 is complete: twelve of twelve operators and seven of
  ten top-level milestones. The blueprint moves to B8; this combined initial/
  final-frame task remains unchecked until final transcript equivalence is proved.
  [Sequential acceptance and shared tallies](docs/research/helios-shared-tallies.md)
  now discharge the source Lemma 11 tally obligation. Accepted submissions
  extend the board chronologically; B7 transfers the entire acceptance sequence.
  Common public nonce recipes and valid literal bits explain each submission
  in both worlds. `accepted_sequence_tally_numeric` proves that the actual E6
  result is one common numeral bounded by the number of voters, for arbitrary
  finite public submission lists and positive candidate counts. Full build:
  3612 jobs, twenty new theorem audits, eight controls and ten definition checks.
  The gate catches replay, count and binding defects, then passes three seeds
  and 2048 inputs. Final-frame static equivalence with public partial
  decryptions remains open; B8 and this task remain unchecked. Coverage stays
  seven of ten milestones. Adaptive-process flattening still needs its proof.
  [Published-frame construction](docs/research/helios-published-frames.md)
  now defines the actual four-handle partial frame and five-handle final frame,
  retaining all initial values and every candidate slot. The public result
  recipe equals the actual appended result tuple. `final_frame_staticEq_iff_partial`
  reduces final equivalence exactly to aggregate-partial frame equivalence;
  it does not assert the remaining premise. Public initial recipes cannot
  reconstruct trustee partials. An individual-partial leak with equal total
  tallies and a missing-slot control retain the publication boundary.
  Full build: 3617 jobs, thirty new theorem audits, eight SPOTs and six
  definition checks. Two gate defects are caught before three seeds and 2048
  inputs pass. B8 and this task remain unchecked; current frontier is the
  aggregate-partial frame theorem, with coverage unchanged at seven of ten.
  [Trustee-partial boundary](docs/research/helios-trustee-partial-boundary.md)
  now excludes initial ciphertexts keyed by an unpublished trustee partial.
  For accepted sequences, a partial matches any initial public recipe exactly
  at its full aggregate binding; matches and partial-slot equality transfer
  across the vote swap. Actual successful boundary probes return one shared
  bounded numeral. Public extended-frame E5 construction remains possible and
  is retained by a control. Full build: 3620 jobs, seventeen new theorem audits
  and eight SPOTs; both gate defects are caught, then three seeds and 2048
  inputs pass. Arbitrary nested new-handle observations remain unproved;
  B8 and this task stay unchecked at seven of ten milestones.
  [Published-frame name protection](docs/research/helios-published-protection.md)
  now handles all nested public recipes in the actual partial frame and, for
  public submissions, the final frame. The E-valued invariant tolerates valid
  raw-unsafe candidate syntax and retains both E5/E6. It excludes restricted
  names and composition factors, constructed election keys and constructed
  trustee partials, without freshness or acceptance assumptions. Full build:
  3626 jobs, forty-two new theorem audits, eleven SPOTs and three definition
  checks; two defects are caught before three seeds and 2048 gate inputs pass.
  Extended value origins and all cross-world recipe equalities remain open;
  B8 and this task stay unchecked at seven of ten milestones.
  [Individual published handles](docs/research/helios-expanded-published-frames.md)
  now preserve exactly the actual final frame's public observations via both
  translations. The exact iff permits proving the same B8 target in that
  presentation. Minimum recipes for published values have one node; minimum
  trustee-partial values are partial-slot handles in accepted elections.
  Semantic E6 with a borrowed trustee partial has a shorter result-handle
  recipe. Costs do not transfer across presentations. Full build: 3631 jobs,
  twenty-eight new theorem audits, ten SPOTs and seven definition checks;
  two gate defects are caught before three seeds and 2048 inputs pass.
  General extended-value origins and all cross-world observations remain
  unproved. B8 and this task stay unchecked at seven of ten milestones.
  [Expanded value origins](docs/research/helios-expanded-value-origins.md)
  now close minimum pair/ciphertext origins and construct actual smaller public
  plaintext certificates. Whole minimum decryptions cannot match E5/E6.
  Minimum partial values are explicit constructors or published partial slots;
  their equality matrix transfers under smaller observations, and minimum
  children give a minimum constructed partial. Accepted public elections
  discharge the numeric-result condition. The existing partial-equality lemma
  now supports any handle count. Full build: 3637 jobs, twenty-five new theorem
  audits, eight SPOTs and one definition check; two gate defects are caught
  before three seeds and 2048 inputs pass. Other value branches, the global
  observation/shared-minimum induction and B8 remain open. Coverage stays
  seven of ten milestones; this task remains unchecked.
  [Expanded public keys](docs/research/helios-expanded-public-keys.md) now have
  exact selector/minimum origins, unique minimum election-key handles and
  minimum constructor closure. The full key equality matrix transfers under
  smaller public argument tests; accepted elections discharge numeric results.
  Initial and expanded frames reuse the structural key-origin proof. Eight
  SPOTs retain nested published arguments, both necessary-premise mutations,
  nonconstant equality and successful structured-key E5. Nineteen new theorem
  audits and one definition check are integrated. Full build: 3642 jobs,
  1926 nonempty standard-only axiom reports and 20 axiom-free reports. Both
  gate mutations are detected before three seeds and 2048 inputs pass. B8
  and this task remain open at seven of ten milestones.
  [Expanded proof values](docs/research/helios-expanded-proof-values.md) now
  have exact minimum constructed/borrowed forms. Mixed aliases are excluded
  by published nonce protection; four minimum arguments give a minimum proof
  constructor. The equality matrix compares all four constructed arguments
  under smaller observations and reuses B7 for borrowed proofs. Initial and
  expanded frames share the structural proof-origin argument, and constructed
  proof equality now supports any handle count. Twenty-two new theorem audits,
  eight controls and two definition checks are integrated. Full build: 3647
  jobs, 1948 nonempty standard-only axiom reports and 20 axiom-free reports.
  Three gate mutations are detected before three seeds and 2048 inputs pass.
  B8 and this task remain unchecked at seven of ten milestones.
  [Expanded pair values](docs/research/helios-expanded-pair-values.md) now
  have exact minimum constructed/nonempty-tail forms and pair values in both
  worlds. Their equality matrix uses smaller projection comparisons and old
  tail identity. The generic constructed-pair comparison now accepts any
  handle count. Eighteen new theorem audits, eight controls and one definition
  check are integrated. Full build: 3651 jobs, 1966 nonempty standard-only
  axiom reports and 20 axiom-free reports. Three gate mutations are detected
  before three seeds and 2048 inputs pass. Empty-tail coincidence,
  invalid eta and borrowed minimum compression remain explicit. Pair-root
  shared minimum transport and the global induction remain open. B8 and this
  task stay unchecked at seven of ten milestones.
  [Expanded atomic values](docs/research/helios-expanded-atomic-values.md)
  now include result-handle constant aliases alongside literal atoms. Minimum
  names remain literal. Accepted shared numeric tallies discharge atomic
  observation transport without smaller tests. Full-E equality replaces the
  invalid raw-literal expectation, retained as a control after the gate exposed
  `0 + 0`. Seventeen new theorem audits and eight controls pass. Full build:
  3655 jobs, 1983 nonempty standard-only axiom reports and 20 axiom-free reports;
  two gate mutations are detected before three seeds and 2048 inputs pass.
  Other value branches, shared minima, global induction and B8 remain open.
  This task stays unchecked at seven of ten milestones.
  [Expanded check values](docs/research/helios-expanded-check-values.md)
  now have exact stuck-check origins, reusing one structural argument for
  initial and expanded frames. Successful minimum projections select old
  honest fields or nonempty tails. Stuck checks of minimum children are
  minimum, and smaller whole-check/ok probes plus three ordered argument
  comparisons transfer their equality. Seventeen new theorem audits, eight
  controls and one definition check are integrated. Full build: 3660 jobs,
  2000 nonempty standard-only axiom reports and 20 axiom-free reports. Two gate
  mutations are detected before three seeds and 2048 inputs pass.
  Failed-decryption shape reflection, other value branches, shared
  minima and global B8 induction remain open. This task stays unchecked at
  seven of ten milestones.
  [Expanded ciphertext key witnesses](docs/research/helios-expanded-ciphertext-keys.md)
  now supply strict smaller public keys and conditional forward ciphertext-value
  transport for actual accepted expanded minimum recipes. Existing syntax and
  homomorphic inversion discharge products; actual honest selectors discharge
  the generic leaf premise. Twelve new theorem audits include six controls,
  retaining raw-unequal E-equal keys, distinct-key nonfusion, repeated factors
  and a countermodel to omitting smaller key observations. The gate passes
  seeds 1/7/42 and 2048 inputs after detecting both mutations at input 0.
  Full build: 3664 jobs, 2012 nonempty standard-only axiom reports and 20
  axiom-free reports; 1046 public theorem entries and 56 current-status docs.
  Log: `tmp/variable-overlap/expanded-cipher-key-full-build.log`. General shape
  reflection, borrowed trustee E6 failure, full ciphertext equality and global
  shared-minimum/observation induction remain open. B8 stays partial; blueprint
  coverage remains seven of ten completed milestones (70% unweighted).
  [Expanded value shapes and decryption](docs/research/helios-expanded-value-shapes.md)
  now close simultaneous pair/ciphertext/partial reflection and equivalences
  for source-minimum recipes under the strict recipe-size observation budget.
  Both numeric-result premises are discharged for accepted elections. Any
  remaining destination match is borrowed E6 and returns its published numeric
  result. A separate whole-decryption/result-handle probe, requiring size plus
  two, contradicts source minimality; the ordinary two-decryption comparison
  budget supplies that allowance and closes syntactic decryption equality.
  The shared structural induction also checks the unchanged initial-frame
  theorem statements. Twenty new audits include eight controls, retaining
  E5 data output, full E6 binding, nonliteral numbers and the strict probe
  budget. Gate: both mutations detected at input 0; seeds 1/7/42 and 2048
  deterministic inputs pass. Full build: 3670 jobs, 2032 nonempty standard-only
  axiom reports, 20 axiom-free reports, 1066 public theorem entries and 57
  current-status docs. Log: `tmp/variable-overlap/expanded-shape-full-build.log`.
  Arbitrary stuck-decryption value origins, projection observations, remaining
  ciphertext/arithmetic branches and global shared minima/observations stay
  open. B8 remains partial; blueprint coverage stays seven of ten (70%).
  [Expanded stuck values](docs/research/helios-expanded-stuck-values.md) now
  derive exact projection/decryption origins from arbitrary minimum stuck
  values, retaining the exact selector and ordered arguments. Stuck
  constructors of minimum children are minimum. Both accepted equality
  branches use the ordinary strict two-recipe observation budget; projection
  failure comes from shape reflection, decryption failure from the existing
  result-handle probes. The shared origin helpers preserve all four original
  initial-frame public theorem statements. Nineteen new audits include nine
  controls, with one definition check. Gate mutations fail at input 0 and
  seeds 1/7/42 plus 2048 inputs pass. Full build: 3675 jobs, 2051 nonempty
  standard-only axiom reports, 20 axiom-free reports, 1085 public theorem
  entries and 58 current-status docs. Log:
  `tmp/variable-overlap/expanded-stuck-full-build.log`. Full ciphertext and
  arithmetic observations, shared minimum transport and global induction
  remain open; successful cases still need integration. B8 remains partial; blueprint
  coverage stays seven of ten completed milestones (70% unweighted).
  [Expanded composition](docs/research/helios-expanded-composition.md) now
  derives source/destination compose origins at the recipe-only observation
  budget, using numeric E6 output exclusion rather than unsupported failure.
  Existing full-E factor bags and leaf-cost equalities supply the complete
  conditional composition-valued equality branch and constructor minimum
  closure. Repeated occurrences retain their costs. Eighteen new audits include
  eight controls, retaining hidden compositions, E5 composition output, actual
  numeric E6 success and a countermodel to omitting handle exclusion. Both gate
  mutations fail at input 0; seeds 1/7/42 and 2048 inputs pass. Full build: 3680
  jobs, 2069 nonempty standard-only axiom reports, 20 axiom-free reports, 1103
  public theorem entries and 59 current-status docs. Log:
  `tmp/variable-overlap/expanded-compose-full-build.log`. Addition and
  multiplication/ciphertext observations, shared minimum transport, successful
  cases and global induction remain open. B8 stays partial and blueprint
  coverage remains seven of ten completed milestones (70% unweighted).
  [Expanded addition equality](docs/research/helios-expanded-addition.md) now
  includes numeric result handles, exact summaries with optional-zero presence,
  and both worlds' nonnumeric atom conditions within the original pair-size
  bound. Full `lake build` passes (3687 jobs), with 24 new theorem audits,
  four definition checks and ten kernel controls. The gate detects all three
  mutations and passes three seeds plus 2048 deterministic inputs. The claim
  checker covers 1127 public theorem entries and 60 current-status documents;
  2093 nonempty axiom reports use only standard axioms, with 20 axiom-free.
  The subsequent minimum representative result below handles cheap published
  numerals; checked controls
  refute reusing literal numeric costs or assuming minimum-child closure.
  [Expanded addition minimum transport](docs/research/helios-expanded-addition-minima.md)
  now supplies a shared source-minimum representative with no smaller-observation
  premise. The least attainable numeric cost handles one-node published values;
  exact summary realization and minimum atom costs prove global minimality.
  Global closure passes 948 jobs and eight controls pass 1063 jobs. The gate
  detects greedy/literal-cost/free-zero defects and passes three seeds plus
  4096 deterministic inputs. Thirty-one theorem audits and three definition
  checks are integrated in full `lake build` (3692 jobs), with 2124 nonempty
  standard-only axiom reports, 20 axiom-free reports, 1158 theorem entries and
  61 current-status documents. Log: `tmp/variable-overlap/expanded-add-min-full-build.log`.
  The subsequent comparison branches are checked below; remaining B8 work
  includes shared minima, successful-case integration and global induction.
  [Expanded multiplication equality](docs/research/helios-expanded-multiplication.md)
  now closes the conditional non-ciphertext product branch. The initial-frame
  structural origin proof is shared; numeric E6 outputs permit destination
  origins at the original recipe-size bound. Existing normal fusion partitions
  and strictly smaller public group comparisons reassemble equality. The gate
  passes 1046 jobs and the final equality target passes 945 jobs; nineteen new
  theorem audits and nine controls are integrated in full `lake build`
  (3698 jobs). The log has 2143 nonempty standard-only axiom reports and 20
  axiom-free reports; the checker covers 1177 theorem entries and 62 current
  status documents. Log: `tmp/variable-overlap/expanded-mul-full-build.log`.
  Multiplication shared minimum transport and the global B8 induction remain open;
  the conditional ciphertext branch is checked below.
  [Expanded ciphertext group comparisons](docs/research/helios-expanded-ciphertext-groups.md)
  now classify all nine constructed/honest/mixed cases with explicit key tests,
  exact honest occurrence bags, public nonce equality and zero-padded mixed
  payloads. Existing groups and merge/observation laws support any handle count;
  the shared nonce-separation proof now accepts normal outer-factor protection
  from opaque published values. The gate passes 1048 jobs and expanded group
  equality passes 931 jobs. Full `lake build` passes 3703 jobs, integrating
  twenty new theorem audits and ten controls with 2163 nonempty standard-only
  axiom reports, 20 axiom-free reports, 1197 public theorem entries and 63
  current-status documents. Log: `tmp/variable-overlap/expanded-group-full-build.log`.
  The expanded assembly connection is now checked below; other B8
  transport/induction work remains open.
  [Expanded ciphertext assemblies](docs/research/helios-expanded-ciphertext-assemblies.md)
  now close conditional minimum ciphertext equality in accepted expanded frames.
  Exact assemblies, public selected keys and original-size group bounds are
  derived from source minima; existing destination ciphertext-value transport
  supplies common-key agreement in both worlds. Strictly smaller public tests
  transfer both key equality and the complete group matrix. Generic assembly
  interpretation reuses E3 and the existing merge laws. The gate passes 1050
  jobs, the complete conditional theorem 943 jobs, and eight kernel controls
  1080 jobs. Full `lake build` passes 3709 jobs, with twenty-one new theorem
  audits, two definition checks, 2184 nonempty standard-only axiom reports and
  20 axiom-free reports. Claim coverage is 1218 public theorem entries and 64
  current-status documents. Log: `tmp/variable-overlap/expanded-assembly-full-build.log`.
  Multiplication shared minimum transport, remaining shared minima,
  successful-case integration and global B8 induction remain open; B9/B10
  remain open. Blueprint coverage stays seven of ten (70% unweighted).
  [Expanded minimum observation assembly](docs/research/helios-expanded-observation-assembly.md)
  now combines all twelve normal operator heads plus names/constants. The
  forward theorem derives its common normal value; reversed acceptance follows
  from B7 and both-world minima supply the equality iff. Exact lifting reduces
  expanded/final/partial static equivalence to two-way shared minima, with a
  bounded interface supplying every smaller observation. The initial gate
  refuted raw-normalization completeness on an actual numeric result; the
  corrected E0-summary oracle retains that fixture and a kernel counterexample.
  Four mutations are detected; three seeds and 2048 deterministic inputs pass.
  Complete assembly/lifting passes 968 jobs, ten controls pass 1089 jobs, and
  full `lake build` passes 3713 jobs. Nineteen new theorem audits bring coverage
  to 1237 entries and 65 current-status documents, with 2203 nonempty
  standard-only axiom reports and 20 axiom-free reports. Log:
  `tmp/variable-overlap/expanded-observation-full-build.log`.
  Two-way shared minima, including multiplication and remaining local/successful
  transport, remain open. B8/B9/B10 remain incomplete; blueprint coverage stays
  seven of ten (70% unweighted).
  [Expanded non-ciphertext multiplication minima](docs/research/helios-expanded-multiplication-minima.md)
  now close the local product transport case with source-minimum children and
  only forward shared minima below the original product size. Source normal
  partitions preserve fusion groups and exact occurrences; generic shared
  reassembly and competitor comparison prove global source minimality. Initial
  wrappers retain their public statements and reuse the same extracted proofs.
  The gate passes 1052 jobs, generic refactoring 893 jobs, expanded closure 944
  jobs and eight controls 1076 jobs. A minimum-child eleven-node product shrinks
  to at most eight nodes; duplicate published-result wrappers shrink from nine
  to exactly three while retaining both factors. Full `lake build` passes
  3716 jobs, integrating seventeen new theorem audits with 2220 nonempty
  standard-only axiom reports and 20 axiom-free reports. Claim coverage is
  1254 entries and 66 current-status documents. Log:
  `tmp/variable-overlap/expanded-mul-min-full-build.log`.
  Ciphertext-valued multiplication, remaining local/successful shared minima
  and global two-way transport remain open. B8/B9/B10 remain incomplete;
  blueprint coverage stays seven of ten (70% unweighted).
  [Expanded constructed ciphertext minima](docs/research/helios-expanded-constructed-minima.md)
  now prove global constructor minimum closure and local shared transport with
  no smaller premises. Opaque public nonce provenance and selected-key/group
  bounds exclude cheaper competitors. Constructed-only products compress
  strictly and share minima under the exact two smaller-minimum hypotheses;
  existing syntax key transfer handles nonminimum assemblies and supplies
  destination values. The gate passes 1053 jobs, core minima/compression 971
  jobs, and eight controls plus public-nonce origins 1094 jobs. Controls prove
  actual four-node published constructors minimum and compress nine-node
  products to six-node global shared minima while retaining duplicate nonces.
  Full `lake build` passes 3721 jobs, integrating twenty-two new theorem audits
  with 2241 nonempty standard-only axiom reports and 21 axiom-free reports.
  Claim coverage is 1276 public theorem entries and 67 current-status documents.
  Log: `tmp/variable-overlap/expanded-constructed-full-build.log`.
  Honest-only/mixed ciphertext multiplication, remaining local/successful
  transport and global two-way minima remain open. B8/B9/B10 remain incomplete;
  blueprint coverage stays seven of ten (70% unweighted).
  [Expanded honest ciphertext minima](docs/research/helios-expanded-honest-minima.md)
  now prove global minimum size and shared representatives for all honest
  selector combinations after accepted publication. Exact indexed occurrences
  fix competitor costs; nonminimum ciphertext products of minimum children
  have constructed-or-mixed groups. Eight kernel controls retain duplicates,
  nonliteral votes, nonempty accepted submissions and countermodels for nonce
  collisions and arbitrary ciphertext publication. The three-mutation gate
  passes seeds 1/7/42 and 2048 deterministic inputs. Mixed ciphertext products,
  remaining local/successful transport and the global two-way induction remain
  open; B8/B9/B10 stay incomplete and milestone coverage remains 7/10.
  Integrated honest-minimum evidence: full `lake build` passes 3725 jobs;
  2259 standard-only nonempty axiom reports and 21 axiom-free reports;
  claim coverage is 1294 public theorem entries and 68 current-status documents.
  [Expanded mixed compression](docs/research/helios-expanded-mixed-compression.md)
  now closes mixed ciphertext assemblies with at least two public constructors
  under two-way smaller minima. Minimum mixed competitors have one constructor,
  exact honest occurrence bags, nonce equality and zero-padded payload equality;
  regrouping preserves their exact minimum size. One-node payloads and minimum
  nonces give global mixed minima over actual published handles. Eight kernel
  controls include twelve-to-nine compression and a one-constructor parent
  with minimum children that still shrinks from nine nodes to seven. The gate
  detects three mutations and passes three seeds plus 2048 deterministic inputs.
  Remaining: general one-constructor padded payload minima with published
  numeric costs, local/successful transport and the global two-way induction.
  B8/B9/B10 remain incomplete; milestone coverage stays 7/10.
  Integrated mixed-compression evidence: full `lake build` passes 3730 jobs;
  2280 nonempty standard-only axiom reports and 21 axiom-free reports;
  claim coverage is 1315 public theorem entries and 69 current-status documents.
  [Expanded padded payload minima](docs/research/helios-expanded-padded-minima.md)
  now give global padded minima with published numeric costs, preserving atom
  occurrences and shared padded values. They close the one-constructor mixed
  case; all expanded multiplication classes are now assembled under two-way
  smaller minima. Eight kernel controls include actual published zero/two,
  repeated atoms, the non-greedy optimum, unpadded cancellation rejection and
  the seven-node minimum for the formerly unresolved mixed input. Three
  mutations are detected; three seeds and 4096 independently checked cost
  inputs pass. Pair/selector and successful-case transport and the global
  simultaneous induction remain open. B8/B9/B10 stay incomplete; coverage 7/10.
  Integrated padded-minimum evidence: full `lake build` passes 3735 jobs;
  2299 standard-only nonempty axiom reports and 21 axiom-free reports;
  claim coverage is 1334 public theorem entries and 70 current-status documents.
  [Expanded pair/selector minima](docs/research/helios-expanded-pair-selector-minima.md)
  now close pairing and both selectors without smaller-test premises. Honest
  field matches reuse B7; nonempty tails retain exact syntax/size, and empty
  tails use bottom. All local roots and simultaneous induction are assembled
  conditionally. Only successful decryption/checking transport in both directions
  remains for expanded, partial and final equivalence. Nine kernel controls
  include five-to-one pair compression, four-to-three aggregate aliasing,
  actual published handles, and an inhabited conditional final-frame pipeline.
  Three mutations and three seeds plus 2048 directed inputs pass. B8 local
  operator coverage is 10/12; B8/B9/B10 remain open and top-level coverage 7/10.
  Integrated pair/selector evidence: full `lake build` passes 3743 jobs;
  2328 nonempty standard-only axiom reports and 21 axiom-free reports;
  claim coverage is 1363 public theorem entries and 71 current-status documents.
  [Expanded successful checks](docs/research/helios-expanded-successful-checks.md)
  close `checkspk` with exactly two-way smaller minima. Constructed proofs reuse
  four public comparisons; honest bindings retain indexed occurrences without
  oversized observations. Expanded/partial/final equivalence now requires only
  successful decryption transport in both directions. Nine kernel controls
  cover actual partial/result inputs, rejected tally two, whole-ciphertext
  binding, reordering, aliases, recipe-size bounds and an inhabited reduced
  pipeline. Three mutations and three seeds plus 2048 inputs pass. B8 local
  coverage is 11/12; B8/B9/B10 remain open and top-level coverage stays 7/10.
  The successful-check integrated build passes 3747 jobs: 1382 public theorem
  audits, 2347 standard-only nonempty and 21 axiom-free reports, 72 current-status
  documents and 914 valid local links. All six changed Lean modules have current
  oleans; no holes/custom axioms/warnings/errors are present and diffcheck passes.
  Log: `tmp/variable-overlap/expanded-successful-check-full-build.log`.
  [Expanded public decryption](docs/research/helios-expanded-public-decryption.md)
  now closes direct E5 and constructed-partial E6, retaining structured keys
  and actual plaintext children. Complete borrowed trustee binding is the
  remaining local premise, at the original strict bound. B7 proves it for all
  retained old recipes; nested new-handle binding remains open. All three
  frame presentations are connected conditionally to the two binding directions.
  Eight controls retain actual public/borrowed partials, the nonconstructed
  honest-product case, incomplete-binding rejection, wrappers, a tally of two
  and an inhabited reduced pipeline. Three mutations, three seeds and 2048
  deterministic inputs pass. B8 stays 11/12 locally and 7/10 top-level.
  The public-decryption integrated build passes 3751 jobs: 1400 audited public
  theorems, 2365 standard-only nonempty and 21 axiom-free reports, 73 documents
  and 932 valid local links. All six changed Lean modules have current oleans;
  no proof holes/custom axioms/warnings/errors were found and diffcheck passes.
  Log: `tmp/variable-overlap/expanded-public-decryption-full-build.log`.
  [Result-handle realization](docs/research/helios-result-handle-binding.md)
  now gives every nested public old-plus-results recipe one shared public
  initial realization. B7 transfers all equality observations and complete
  tally binding with no minimum/size hypothesis. The remaining trustee-binding
  callback is restricted to minimum ciphertexts without a result-only
  presentation. A real accepted result of two supplies the nonce of a ten-node
  minimum tally match; it has no old-only preimage and numeral expansion costs
  fourteen nodes. Nine controls retain this alias, nested numeric realization,
  noncollapsed equivalence, failed partial erasure and an inhabited callback.
  Three mutations, three seeds and 2048 directed inputs pass. B8 remains 11/12
  locally, with trustee-dependent binding open; top-level coverage stays 7/10.
  The result-handle integrated build passes 3756 jobs: 1424 audited public
  theorems, 2389 standard-only nonempty and 21 axiom-free reports, 74 documents
  and 951 valid local links. All seven changed Lean modules have current oleans;
  no proof holes/custom axioms/warnings/errors were found and diffcheck passes.
  Log: `tmp/variable-overlap/result-handle-binding-full-build.log`.
  The all-position trustee-free invariant now proves that minimum full-tally
  bindings have exact old-plus-results syntax. E7 retains every component;
  minimum destructors cannot erase a partial except for old-handle projections.
  Shared numeric realization completes trustee binding and static equivalence
  of all three published presentations. Forty-eight new theorem audits include
  ten kernel controls. Three known defects are detected and three seeds plus
  2048 directed inputs pass. B8 is complete: 12/12 local roots and 8/10 top-level
  milestones. The full process/secrecy theorem remains open in the next task.
  The B8 completion build passes 3766 jobs: 1472 audited public theorems,
  2437 standard-only nonempty and 21 axiom-free reports, 75 documents and
  946 valid local links. All twelve changed Lean sources have
  current oleans, with no holes/custom axioms/warnings/errors. Diffcheck passes.
  Log: `tmp/variable-overlap/trustee-free-full-build.log`.
  The earlier proof-suffix full `lake build` passes (3542 jobs), with eighteen new theorem audits,
  seven controls and the extended proof-suffix gate in both swaps.
  The local-root full `lake build` passes (3537 jobs), with sixteen new theorem
  audits, seven controls and the bounded competitor gate in both swaps.
  The assembly's full `lake build` passes (3533 jobs), with sixteen
  new theorem audits and eight controls. See the
  [assembly record](docs/research/helios-observation-assembly.md). A checked
  child/minimum comparison costs nine nodes against an eight-node parent
  observation, so smaller children alone do not justify that transport.
  See the [minimum-transport criterion](docs/research/helios-minimum-transport.md).
  Its full `lake build` passes (3529 jobs), with 19 new theorem audits,
  eight controls and the 4096-model finite backstop.
  The global smaller-observation premise and full historical arbitrary-recipe
  closure remain open. The multiplication build passes (3525 jobs), including 39 new theorem audits
  and twelve controls. See the
  [multiplication record](docs/research/helios-multiplication-observations.md),
  [addition record](docs/research/helios-addition-observations.md),
  [composition record](docs/research/helios-composition-observations.md),
  [value-shape record](docs/research/helios-value-shapes.md),
  [decryption probe record](docs/research/helios-decryption-probes.md),
  [stuck-destructor record](docs/research/helios-stuck-destructors.md),
  [destructor record](docs/research/helios-destructor-observations.md),
  [atomic record](docs/research/helios-atomic-observations.md),
  [pair record](docs/research/helios-pair-observations.md),
  [partial-decryption record](docs/research/helios-partial-decryption-observations.md),
  [public-key record](docs/research/helios-public-key-observations.md),
  [proof induction record](docs/research/helios-proof-observations.md),
  [ciphertext induction record](docs/research/helios-ciphertext-observations.md),
  [grouping record](docs/research/helios-ciphertext-grouping.md),
  [mixed-ciphertext record](docs/research/helios-mixed-ciphertexts.md),
  [enriched-ciphertext record](docs/research/helios-enriched-ciphertexts.md) and
  [static-transfer interfaces](docs/research/helios-static-equivalence.md).
- [x] **Complete B9/B10: historical source matching and parametrized symbolic
  ballot secrecy.** scopedVoterElection_ballot_secrecy proves source weak labelled
  bisimilarity of the actual repaired historical scoped elections, for arbitrary
  valid ground candidates and finite administration size under documented name,
  nonce/parameter and channel freshness. All correspondence, frame and action
  obligations are discharged; the source weak-bisimulation definition, theorem,
  positive/negative controls, required full build and audits pass. The next task
  is the retrospective reuse audit below. The following progress paragraphs
  are historical and their earlier open-status claims are superseded here.
  The [twelve-stage model](docs/research/helios-process-stages.md) now proves
  reachable accepted/public histories, voter bounds, fresh output domains,
  public input scope, two-way same-label transition matching and static
  equivalence of every reachable frame. Ten kernel controls reach completed
  zero/two-input elections and replay rejection; missing voters cannot be
  skipped. Four mutations are detected and three seeds plus 2048 directed
  executions pass the bounded fixture gate. Next: prove source-calculus
  operational correspondence for substitutions, private trustee payloads,
  restrictions, structural rules and fresh binders; then assemble source
  labelled bisimilarity. This task stays unchecked; coverage remains 8/10.
  The integrated process-stage build passes 3771 jobs: 1500 audited public
  theorem entries, 2464 standard-only nonempty and 22 axiom-free reports,
  76 documents and 962 local links. All seven changed Lean
  sources have current oleans; no holes/custom axioms/warnings/errors were
  found and diffcheck passes. Log:
  `tmp/variable-overlap/process-stages-full-build.log`.
  [Source input/payload correspondence](docs/research/helios-source-payloads.md)
  now proves capture-avoiding term input substitution and composition, private
  variable renaming, public-handle-preserving local flattening, and exact source
  tally/trustee/result agreement. Source output frames inherit B8 with its
  explicit protocol premises. Ten controls include nested binders, semantic
  wrong-candidate rejection and actual zero/one/two tallies. Three mutations,
  three seeds and 2048 directed inputs pass. Next remains process-level source
  syntax and operational correspondence under structural rules, restrictions
  and fresh binders, followed by labelled bisimilarity. B9/B10 stay unchecked.
  The source-payload integrated build passes 3776 jobs: 1532 audited public
  theorem entries, 2494 standard-only nonempty and 24 axiom-free reports,
  77 documents and 977 local links. All seven changed Lean
  sources have current oleans; no holes/custom axioms/warnings/errors were
  found and diffcheck passes. Log:
  `tmp/variable-overlap/source-payload-full-build.log`.
  [Source process binding](docs/research/helios-source-processes.md) now adds a
  finite static-channel AST, process substitution identity/composition and
  input/renaming laws, full-E source guards and public-guard transport, and
  direct ground communication/conditional rules with inversion. Ten kernel
  controls reject capture, wrong-channel communication and syntactic guard
  decisions; trustee/result exchanges reuse the actual payload bodies. Next:
  election residuals, extended substitutions, restriction/structural rules,
  visible labels and fresh output binders, then source labelled bisimilarity.
  B9/B10 stay unchecked; the direct core rules do not yet establish source
  operational correspondence.
  The source-process integrated build passes 3779 jobs: 1559 audited public
  theorem entries, 2518 standard-only nonempty and 27 axiom-free reports,
  78 documents and 985 local links. All five changed Lean sources have current
  oleans; no holes/custom axioms/warnings/errors were found and diffcheck passes.
  Log: `tmp/variable-overlap/source-process-full-build.log`.
  [Literal source election bodies](docs/research/helios-source-election.md) now
  provide the complete finite board/trustee and a finite formula exactly
  equivalent to corrected `Accepted`. Generator substitution and input binding
  retain arbitrary remaining voters, and direct communication/check lemmas
  preserve all source outputs and stop-on-rejection. B7 transfers the actual
  finite public guard. Twelve kernel controls include real final-input acceptance,
  omitted-board and cross-candidate replay negatives, and zero/one results.
  Next remains whole-election residuals, extended substitutions, structural and
  restriction correspondence, visible labels/fresh output variables, then
  source labelled bisimilarity. B9/B10 stay unchecked at 8/10 milestones.
  The source-election integrated build passes 3784 jobs: 1601 audited public
  theorem entries, 2556 standard-only nonempty and 31 axiom-free reports,
  79 documents and 995 local links. All seven changed Lean sources have current
  oleans; no holes/custom axioms/warnings/errors were found and diffcheck passes.
  Log: `tmp/variable-overlap/source-election-full-build.log`.
  [Source parallel structure and residuals](docs/research/helios-source-parallel.md)
  now characterize the parallel laws and their internal closure exactly in both
  directions. All twelve stage forms have literal process residuals, and every
  internal stage transition is realized in the whole election body. Rejected
  and completed residuals are internally quiet; the rejected trustee is retained.
  Ten kernel controls preserve multiplicity/sequence and reject hidden or
  wrong-channel reductions, with real honest/private handshakes. Next: converse
  election-step classification, visible labels, restriction and extended-source
  correspondence, then labelled bisimilarity. B9/B10 stay unchecked at 8/10.
  The source-parallel integrated build passes 3791 jobs: 1647 audited public
  theorem entries, 2597 standard-only nonempty and 36 axiom-free reports,
  80 documents and 1005 local links. All nine changed Lean sources have current
  oleans; no holes/custom axioms/warnings/errors were found and diffcheck passes.
  Log: `tmp/variable-overlap/source-parallel-full-build.log`.
  [Exact internal source correspondence](docs/research/helios-source-internal.md)
  now covers both directions for all in-range residuals under explicit channel
  separation. Arbitrary Tau targets retain the exact stage residual up to ParEq,
  and actual source internal steps match between voting worlds. Eleven kernel
  controls retain real accepted/replayed outcomes and show failures when channel
  separation or range is omitted. Next: public labels/fresh exported variables,
  private restrictions and the extended-source substitution/scope bridge, then
  source labelled bisimilarity. B9/B10 stay unchecked at 8/10 milestones.
  The source-internal integrated build passes 3798 jobs: 1681 audited public
  theorem entries, 2631 standard-only nonempty and 36 axiom-free reports,
  81 documents and 1016 local links. All nine changed Lean sources have current
  oleans; no holes/custom axioms/warnings/errors were found and diffcheck passes.
  Log: `tmp/variable-overlap/source-internal-full-build.log`.
  [Scoped visible actions](docs/research/helios-source-scoped.md) now provide
  exact prefix/context rules and an evaluated frame wrapper with public-recipe
  input labels, fresh-handle output labels, exact payload retention and old-value
  preservation. Fixed private-channel filtering blocks visible interactions but
  retains Tau; actual voter input/publication prefixes are realized and the
  rejected trustee has no wrapper event. Eleven controls include a visible leak,
  redaction rejection and a private handshake. Next: full visible/captured-frame
  correspondence and source active-substitution/scope derivation, then source
  labelled bisimilarity. B9/B10 stay unchecked at 8/10 milestones.
  The source-scoped integrated build passes 3804 jobs: 1721 audited public
  theorem entries, 2666 standard-only nonempty and 41 axiom-free reports,
  82 documents and 1026 local links. All nine changed Lean sources have current
  oleans; no holes/custom axioms/warnings/errors were found and diffcheck passes.
  Log: `tmp/variable-overlap/source-scoped-full-build.log`.
  [Exact visible correspondence](docs/research/helios-source-visible.md) now
  classifies every public input/output in the evaluated election wrapper, with
  full payloads and arbitrary targets modulo ParEq. Each output captures exactly
  the next source view; reached source views inherit B7/B8 observations. Nine
  controls reject skipped/pending-check inputs, redaction, overwritten handles
  and dropped parallel context. Next: derive source active substitutions,
  atomic output/Comm, restriction/scope, alpha-equivalence and outer voter lets;
  then assemble source weak labelled bisimilarity. B9/B10 stay unchecked at 8/10.
  The source-visible integrated build passes 3811 jobs: 1748 audited public
  theorem entries, 2692 standard-only nonempty and 42 axiom-free reports,
  83 documents and 1040 local links. All nine changed Lean sources have current
  oleans; no holes/custom axioms/warnings/errors were found and diffcheck passes.
  Log: `tmp/variable-overlap/source-visible-full-build.log`.
  [Active substitutions and atomic communication](docs/research/helios-source-active.md)
  now derive full message input from atomic Comm and fresh active lets. Every
  evaluated internal Tau and historical internal stage step has a derivation
  in this variable/active fragment. Export preservation prevents erasing public
  active bindings. Ten controls retain nested/outer variables, compound messages,
  restricted versus exported aliases, honest communication and replay rejection.
  Next: full extended-source converse, name-scope/labelled rules, alpha-equivalence,
  source unique-definition/closedness and outer voter lets, then source weak
  labelled bisimilarity. B9/B10 stay unchecked at 8/10 milestones.
  The source-active integrated build passes 3816 jobs: 1776 audited public
  theorem entries, 2720 standard-only nonempty and 42 axiom-free reports,
  84 documents and 1050 local links. All eight changed Lean sources have current
  oleans; no holes/custom axioms/warnings/errors were found and diffcheck passes.
  Log: `tmp/variable-overlap/source-active-full-build.log`.
  [Atomic output and active frames](docs/research/helios-source-atomic-output.md)
  now derive every evaluated scoped output from Out-Atom/Open-Atom with full
  active payloads and retained context. Variable scope preserves old exports;
  an explicit fresh/last-handle bijection gives the exact extended target frame.
  Eleven controls retain secret/compound payloads, scope crossing, old handles
  and actual honest publication. Next: active-frame recipe input, source unique
  definitions/closedness and outer lets, name scope/alpha, and the full operational
  converse, then source weak labelled bisimilarity. B9/B10 stay unchecked at 8/10.
  The source-atomic-output integrated build passes 3822 jobs: 1811 audited public
  theorem entries, 2753 standard-only nonempty and 44 axiom-free reports,
  85 documents and 1061 local links. All eight changed Lean sources have current
  oleans; no holes/custom axioms/warnings/errors were found and diffcheck passes.
  Log: `tmp/variable-overlap/source-atomic-output-full-build.log`.
  [Recipe input through active frames](docs/research/helios-source-frame-input.md)
  now derives every evaluated scoped input from source In/Subst with the original
  recipe label, exact target and retained frame/context. All recipe variables
  have real exports. Internal steps now also derive beside actual active frames,
  completing forward derivations for every evaluated step kind in this fragment.
  Eleven controls retain compound recipes, opaque keys, nested/outer binders,
  equal-valued handles and actual election inputs/handshakes. Next: source unique
  definitions/closedness and outer lets, name scope/alpha, and the full converse,
  then source weak labelled bisimilarity. B9/B10 stay unchecked at 8/10 milestones.
  The source-frame-input integrated build passes 3826 jobs: 1838 audited public
  theorem entries, 2780 standard-only nonempty and 44 axiom-free reports,
  86 documents and 1070 local links. All six changed Lean sources have current
  oleans; no holes/custom axioms/warnings/errors were found and diffcheck passes.
  Log: `tmp/variable-overlap/source-frame-input-full-build.log`.
  [Source variable well-formedness](docs/research/helios-source-wellformed.md)
  now certifies unique active definitions and closedness for actual frames,
  ground lets and raw captures. All structural/internal/free/bound-output
  targets from actual frame states remain well-formed via complete exported
  domains. Eleven controls reject duplicates/missing aliases/undefined fields;
  a raw-rewrite counterexample refutes arbitrary closedness preservation without
  full domain coverage. Next: name scope/alpha, outer voter construction and
  the full operational converse, then source weak labelled bisimilarity.
  B9/B10 stay unchecked at 8/10 milestones.
  The source-wellformed integrated build passes 3831 jobs: 1886 audited public
  theorem entries, 2826 standard-only nonempty and 46 axiom-free reports,
  87 documents and 1080 local links. All seven changed Lean sources have current
  oleans; no holes/custom axioms/warnings/errors were found and diffcheck passes.
  Log: `tmp/variable-overlap/source-wellformed-full-build.log`.
  [Global name permutations](docs/research/helios-source-name-permutations.md)
  now preserve and reflect full-E equality/disequality and all implemented
  structural/internal/free/bound-output behavior. Independent base/channel
  permutations commute with variable substitution and binder exchange. Twelve
  controls include actual election communication and the noninjective-map
  counterexample. Recipe publicness requires the renamed restriction policy.
  Next connect renamed frames and actual name restriction/scope/alpha, outer
  voter construction and the full operational converse, then source bisimilarity.
  B9/B10 stay unchecked at 8/10 milestones.
  Integrated `lake build`: 3837 jobs; 2880 standard-only and 47 axiom-free
  reports; 1941 theorem entries/88 documents; eight current oleans, 1090 local
  links, no holes/custom axioms/warnings/errors, clean diff check. Added 55
  theorem audits (twelve controls) and six definition checks; targeted 1213 jobs.
  Log: `tmp/variable-overlap/source-name-permutation-full-build.log`.
  [Renamed public observations](docs/research/helios-source-renamed-observations.md)
  now preserve/reflect all-public-recipe static equivalence and every evaluated
  scoped step with exact output values. Actual active frames/processes and raw
  output capture commute with consistent independent name/channel maps. Ten
  controls include compound input, leaked output, private-channel policy and
  actual reached election observations. Next actual name scope/alpha, outer
  voter construction and the full source converse, then weak bisimilarity.
  B9/B10 stay unchecked at 8/10 milestones.
  Integrated `lake build`: 3841 jobs; 2908 standard-only and 47 axiom-free
  reports; 1969 theorem entries/89 documents; six current oleans, 1098 local
  links, no holes/custom axioms/warnings/errors, clean diff check. Added 28
  theorem audits (ten controls) and three definition checks; targeted 1217 jobs.
  Log: `tmp/variable-overlap/source-renamed-observations-full-build.log`.
  [Explicit name restrictions](docs/research/helios-source-name-restrictions.md)
  now provide sorted binders, fresh New/Scope/alpha rules and all forward
  evaluated scoped-step derivations through actual restrictions. Canonical
  binders are distinct, input-policy checks equal label freshness, and output
  keeps every restriction and full captured value. Fourteen controls cover
  scope/alpha and capture-failing premises. Next full structural/alpha converse,
  named observations/admissibility and outer voter nonce/let construction, then
  source weak bisimilarity. B9/B10 stay unchecked at 8/10 milestones.
  Integrated `lake build`: 3846 jobs; 2942 standard-only and 47 axiom-free
  reports; 2003 theorem entries/90 documents; seven current oleans, 1110 local
  links, no holes/custom axioms/warnings/errors, clean diff check. Added 34
  theorem audits (fourteen controls) and 20 definition checks; targeted 1217 jobs.
  Log: `tmp/variable-overlap/source-name-restriction-full-build.log`.
  [Private-channel closure](docs/research/helios-source-channel-closure.md)
  now proves the public-channel converse through every current structural/alpha
  derivation and after arbitrary internal execution. All steps only remove free
  channels. Twelve controls retain public secret output/private communication.
  Four additional alpha-input boundary proofs refute inferring the original
  fixed recipe policy after bound-name renaming. Next fresh representatives
  relative to labels, full payload/target converse, named observations and outer
  voter construction, then source weak bisimilarity. B9/B10 stay unchecked.
  Integrated `lake build`: 3852 jobs; 2996 standard-only and 47 axiom-free
  reports; 2057 theorem entries/91 documents; eight current oleans, 1120 local
  links, no holes/custom axioms/warnings/errors, clean diff check. Added 54
  theorem audits (twelve channel controls and four alpha-input boundary proofs)
  and four definition checks; targeted channel controls 1222 jobs.
  Log: `tmp/variable-overlap/source-channel-closure-full-build.log`.
  [Fresh bound-name representatives](docs/research/helios-source-fresh-names.md)
  now use legal alpha/context rules to avoid every finite label-name set. Both
  worlds share permutations and an exact canonical image policy; public
  channels/free label literals stay fixed. Known inputs retain the original
  recipe/label/target, with publicness at the fresh policy and full frame
  observations preserved. Eleven controls cover nested binders, retained keys
  and actual reached worlds. Next full derivation/target converse from fresh
  representatives, named observations/admissibility and voter construction,
  then weak bisimilarity. B9/B10 stay unchecked at 8/10 milestones.
  Integrated `lake build`: 3859 jobs; 3036 standard-only and 48 axiom-free
  reports; 2098 theorem entries/92 documents; nine current oleans, 1134 local
  links, no holes/custom axioms/warnings/errors, clean diff check. Added 41
  theorem audits (eleven controls) and three definition checks; targeted 1236 jobs.
  Log: `tmp/variable-overlap/source-fresh-names-full-build.log`.
  [Active-variable interpretation](docs/research/helios-source-interpretation.md)
  now preserves every Extended structural rule and recovers an actual Tau from
  every Extended internal reduction. Full-E guard/payload congruence commutes
  with parallel structure; input matching can retain the exact message.
  Canonical frame endpoints preserve every full handle E-value and common-policy
  observations. Fifteen controls retain negative guards, nested binders, the
  nonclosed Rewrite boundary and actual-frame private communication. Next:
  Extended visible/capture interpretation, Named alpha/target correspondence,
  named observations/admissibility and outer voters, then weak bisimilarity.
  B9/B10 remain unchecked at 8/10 milestones.
  Integrated `lake build`: 3869 jobs; 3118 standard-only and 48 axiom-free
  reports; 2180 theorem entries/93 documents; twelve current oleans, 1162 local
  links; no proof holes/custom axioms/warnings/errors; diff check passes.
  Added 82 theorem audits, fifteen controls and five definition checks.
  Log: `tmp/variable-overlap/source-interpretation-full-build.log`.
  [Visible active interpretation](docs/research/helios-source-visible-interpretation.md)
  now covers every current Extended free/bound action through variable Scope,
  Par and arbitrary Struct. Inputs use the exact evaluated recipe; bound outputs
  extend the target with the complete actual emitted message and keep old values.
  Supplied canonical targets preserve every old/new handle E-value and full
  common-policy observations. Fourteen controls include scoped values, old-handle
  mutation rejection and actual first publication. Next Named alpha/restriction
  interpretation, canonical-target existence, named observations/admissibility,
  outer voters and final weak bisimilarity. B9/B10 remain unchecked at 8/10.
  Integrated `lake build`: 3876 jobs; 3156 standard-only and 48 axiom-free
  reports; 2218 theorem entries/94 documents; nine current oleans, 1178 local
  links; no proof holes/custom axioms/warnings/errors; diff check passes.
  Added 38 theorem audits, fourteen controls and one definition check.
  Log: `tmp/variable-overlap/source-visible-interpretation-full-build.log`.
  [Consistent name interpretation and prenex forms](docs/research/helios-source-name-interpretation.md)
  now transport/reflect complete Extended environments, labels and captures.
  Every finite Named process has an outer name prefix and one Extended body;
  the prefix can be fresh and distinct. Thirteen controls reject stale alpha
  environments, false noninjective reflection and unfresh channel extrusion;
  actual fresh worlds retain their full interpretations/observations. Next whole
  Named derivation interpretation, canonical active-frame targets, named
  observations/admissibility, outer voters and final weak bisimilarity.
  B9/B10 remain unchecked at 8/10 milestones.
  Integrated `lake build`: 3883 jobs; 3194 standard-only and 48 axiom-free
  reports; 2256 theorem entries/95 documents; nine current oleans, 1182 local
  links; no proof holes/custom axioms/warnings/errors; diff check passes.
  Added 38 theorem audits and thirteen controls; targeted build 1265 jobs.
  Log: `tmp/variable-overlap/source-name-interpretation-full-build.log`.
  [Named operational factorization](docs/research/helios-source-operational-prenex.md)
  now covers all internal and free actions by actual Extended steps under one
  common prefix, with structural endpoint paths and converse reconstruction.
  Free labels remain exact and fresh for the prefix; distinct variants avoid
  any finite external set. Twelve controls retain actual private communication,
  unchanged alpha input and deep proof-field support. Next bound-output
  factorization, canonical frame/interpretation correspondence, named
  observations/admissibility, outer voters and final weak bisimilarity.
  B9/B10 remain unchecked at 8/10 milestones.
  Integrated `lake build`: 3889 jobs; 3220 standard-only and 48 axiom-free
  reports; 2282 theorem entries/96 documents; eight current oleans, 1195 local
  links; no proof holes/custom axioms/warnings/errors; diff check passes.
  Added 26 theorem audits and twelve controls; targeted build 1271 jobs.
  Log: `tmp/variable-overlap/source-operational-prenex-full-build.log`.
  [Bound-output factorization](docs/research/helios-source-bound-prenex.md)
  now completes all current Named action cases. Injective variable renaming
  transports every Extended/Named structural rule. Bound outputs retain the
  exact channel, exchanged binder and full shifted old context under one common
  prefix, with converse reconstruction and distinct fresh variants. Twelve
  controls include full frame capture and collapsing-variable rejection. Next
  canonical frame/interpretation correspondence, named observations/admissibility,
  outer voters and final weak bisimilarity. B9/B10 remain unchecked at 8/10.
  Integrated `lake build`: 3896 jobs; 3250 standard-only and 49 axiom-free
  reports; 2313 theorem entries/97 documents; nine current oleans, 1209 local
  links; no proof holes/custom axioms/warnings/errors; diff check passes.
  Added 31 theorem audits and twelve controls; targeted build 1278 jobs.
  Log: `tmp/variable-overlap/source-bound-prenex-full-build.log`.
  [General frame projection](docs/research/helios-source-frame-projection.md)
  now retains full active payloads and all restrictions, transports every
  structural rule, preserves internal/free frames and recovers the old frame
  after restricting the fresh bound-output handle. Canonical extraction and
  existence of Extended interpretations from frame constraints are checked.
  Fourteen controls include complete proof fields, alpha, nested output,
  shifted old exports and inconsistent-environment rejection. Next general
  Named observations/admissibility, canonical environment/body correspondence,
  outer voters and final weak bisimilarity; B9/B10 remain unchecked at 8/10.
  Integrated `lake build`: 3902 jobs; 3291 standard-only and 50 axiom-free
  reports; 2355 theorem entries/98 documents; eight current oleans, 1221 local
  links; no proof holes/custom axioms/warnings/errors; diff check passes.
  Added 42 theorem audits and fourteen controls; targeted build 1284 jobs.
  Log: `tmp/variable-overlap/source-frame-projection-full-build.log`.
  [Named variable admissibility](docs/research/helios-source-named-admissibility.md)
  now preserves exported domains and unique definitions through every structural
  rule and internal/free action. Bound output retains old handles and exports
  a defined fresh variable for uniquely defined sources. Canonical Named states
  and all raw targets are well-formed; exact free-label variable scope and
  well-formed complete-domain factored Extended bodies are checked. Sixteen
  controls include missing-definition raw output and full fourth-field scope.
  Next general Named equality observations, canonical environment/body
  correspondence, outer voters and final weak bisimilarity. B9/B10 remain
  unchecked at 8/10; these variable conditions do not assert full admissibility.
  Integrated `lake build`: 3910 jobs; 3353 standard-only and 57 axiom-free
  reports; 2424 theorem entries/99 documents; ten current oleans, 1235 local
  links; no proof holes/custom axioms/warnings/errors; diff check passes.
  Added 69 theorem audits and sixteen controls; targeted build 1292 jobs.
  Log: `tmp/variable-overlap/source-named-admissibility-full-build.log`.
  [Named static witnesses](docs/research/helios-source-named-static.md)
  now give every reached election source stage and arbitrary structural
  representatives Definition 1 common restricted-substitution presentations
  with all-public-recipe full-E equivalence. Internal/free paths preserve the
  witnesses; coherent freshening keeps arbitrary literal recipe tests unchanged.
  Twelve controls include full domains, completed/rejected elections and equal
  frames with different next actions. Next canonical-presentation compatibility/
  reflection, environment/body correspondence, remaining admissibility, outer
  voters and final weak bisimilarity. B9/B10 remain unchecked at 8/10.
  Integrated `lake build`: 3915 jobs; 3391 standard-only and 57 axiom-free
  reports; 2462 theorem entries/100 documents; seven current oleans, 1246 local
  links; no proof holes/custom axioms/warnings/errors; diff check passes.
  Added 38 theorem audits and twelve controls; targeted build 1297 jobs.
  Log: `tmp/variable-overlap/source-named-static-full-build.log`.
  [Complete Named permutations](docs/research/helios-source-named-permutations.md)
  now transport and reflect every structural/action rule, including alpha,
  complete labels and exchanged/shifted bound-output contexts. Full frame and
  static witnesses move with their policies and values, using New-C to reorder
  canonical prefixes. Thirteen controls include collapse/freshness failures,
  exact mapped literals, nested output reflection and private-channel blocking.
  Next compatibility of unrelated canonical presentations, environment/body
  correspondence, remaining admissibility, outer voters and final weak
  bisimilarity. B9/B10 remain unchecked at 8/10.
  Integrated `lake build`: 3920 jobs; 3430 standard-only and 57 axiom-free
  reports; 2501 theorem entries/101 documents; seven current oleans, 1257 local
  links; no proof holes/custom axioms/warnings/errors; diff check passes.
  Added 39 theorem audits and thirteen controls; targeted build 1302 jobs.
  Log: `tmp/variable-overlap/source-named-permutation-full-build.log`.
  [General active substitution](docs/research/helios-source-general-substitution.md)
  now adds the documented missing active-active Subst case and derives the rule
  through all current Extended contexts and fresh Named representatives. Both
  provider and domains remain; full replacement terms avoid variable/name capture.
  Existing invariants, interpretations and permutations are rechecked against
  the expanded source relation. Fourteen controls include dependent-frame
  normalization/ground presentation and rejection of missing providers/capture.
  Next general normalization, unrelated-presentation compatibility, canonical
  environment/body correspondence, remaining admissibility, outer voters and
  final weak bisimilarity. B9/B10 remain unchecked at 8/10; full E is unchanged.
  Integrated `lake build`: 3923 jobs; 3457 standard-only and 57 axiom-free
  reports; 2528 theorem entries/102 documents; fourteen current oleans, 1269 local
  links; no proof holes/custom axioms/warnings/errors; diff check passes.
  Added 27 theorem audits and fourteen controls; new constructor/function
  explicitly checked; targeted build 1143 jobs.
  Log: `tmp/variable-overlap/source-general-substitution-full-build.log`.
  [Local active-definition elimination](docs/research/helios-source-local-normalization.md)
  now constructs exact instantiations and derives removal of a local provider
  through Extended contexts and fresh Named representatives. All surviving
  domains and complete interpretations are retained. Fifteen controls include
  dependent local chains with a ground presentation, input/private-name capture
  avoidance, and wrong-value/duplicate-definition rejection. The provider must
  be independent of its own local binder; unique definitions discharge the
  context side condition. General constraint-system normalization, arbitrary
  presentation compatibility, canonical environment/body correspondence, outer
  voters and final weak bisimilarity remain open. B9/B10 stay unchecked at 8/10.
  Integrated `lake build`: 3927 jobs; 3482 standard-only and 61 axiom-free
  reports; 2557 theorem entries/103 documents; six current oleans, 1279 local
  links; no proof holes/custom axioms/warnings/errors in the checked scope;
  diff check passes. Added 29 theorem audits and fifteen controls; the graph
  definition is explicitly checked; targeted build 1146 jobs.
  Log: `tmp/variable-overlap/source-local-normalization-full-build.log`.
  [Unused restrictions and common policies](docs/research/helios-source-policy-padding.md)
  now align arbitrary independent Named static witnesses under one policy,
  retaining all four source paths and both full frame certificates without
  caller-supplied freshness. Finite unused-policy padding preserves/reflects
  full public equality tests and has actual canonical source paths. Fifteen
  controls include colliding policies, full fourth-field freshness and used
  channel rejection. Middle-frame observation compatibility, canonical
  environment/body correspondence, relevant constraint normalization, outer
  voters and final weak bisimilarity remain open. B9/B10 stay unchecked at 8/10.
  Integrated `lake build`: 3932 jobs; 3520 standard-only and 61 axiom-free
  reports; 2595 theorem entries/104 documents; seven current oleans, 1288 local
  links; no proof holes/custom axioms/warnings/errors in the checked scope;
  diff check passes. Added 38 theorem audits and fifteen controls; both new
  frame definitions are explicitly checked; targeted build 1145 jobs.
  Log: `tmp/variable-overlap/source-policy-padding-full-build.log`.
  [Explicit voter computations](docs/research/helios-source-voter-computation.md)
  now build every candidate and aggregate let, produce the exact historical
  ballot for arbitrary full ground values and normalize to the authenticated
  output through existing source rules. Both honest blocks normalize to the
  allocated initial election with action iff theorems, presentation/WF and
  initial static witnesses. Sixteen controls detect skipped candidate registers
  and nonce swaps and include a real private communication. Next interleaved
  nonce-scope placement, fresh candidate application, explicit board tally lets,
  middle-frame observation compatibility, canonical environment/body
  correspondence and remaining admissibility. B9/B10 stay unchecked at 8/10.
  Integrated `lake build`: 3937 jobs; 3556 standard-only and 62 axiom-free
  reports; 2632 theorem entries/105 documents; seven current oleans, 1298 local
  links; no proof holes/custom axioms/warnings/errors in the checked scope;
  diff check passes. Added 37 theorem audits and sixteen controls; eleven
  construction/compilation definitions checked; targeted build 1144 jobs.
  Log: `tmp/variable-overlap/source-voter-computation-full-build.log`.
  [Explicit board tally computations](docs/research/helios-source-board-tallies.md)
  now bind every candidate product at the tallying stage and normalize to
  boardFinish through actual source rules. Finite pointwise-E environment
  substitution supplies the saved-register/tuple-projection correspondence
  beneath the later trustee input. Full frame witnesses, well-formedness,
  exact action iff interfaces and a real private communication remain explicit.
  Nineteen controls reject omitted/copied candidates and input capture. Next:
  source continuations beneath preceding board inputs/guards, interleaved voter
  nonce scopes, fresh candidate application, independent frame compatibility,
  canonical environment/body correspondence and remaining admissibility.
  B9/B10 stay unchecked at 8/10 milestones.
  Integrated `lake build`: 3942 jobs; 3598 standard-only and 64 axiom-free
  reports; 2676 theorem entries/106 documents; seven current oleans, 1309 local
  links; no proof holes/custom axioms/warnings/errors in the checked scope;
  diff check passes. Added 44 theorem audits and nineteen controls; eleven
  construction/compilation definitions checked.
  Log: `tmp/variable-overlap/source-board-tallies-full-build.log`.
  [Interleaved voter nonce scopes](docs/research/helios-source-voter-scopes.md)
  now normalize to the complete initial election with the real board/trustee,
  public-key frame and exact name/channel policy. Full candidate-term freshness
  is explicit and a common allocation exists for arbitrary ground parameters.
  Action iff interfaces, presentation/WF, initial static witnesses and a real
  private communication are proved. Twenty-five controls cover discarded names,
  full proof fields, scope order and used-channel rejection. Open-voter parameter
  application, preceding board input/guard continuation syntax, independent frame
  compatibility, canonical environment/body correspondence and remaining
  admissibility/action matching stay open. B9/B10 stay unchecked at 8/10.
  Integrated `lake build`: 3951 jobs; 3673 standard-only and 64 axiom-free
  reports; 2751 theorem entries/107 documents; eleven current oleans, 1325 local
  links; no proof holes/custom axioms/warnings/errors in the checked scope;
  diff check passes. Added 75 theorem audits and twenty-five controls; nineteen
  construction/freshness/compilation definitions checked; targeted 1160 jobs.
  Log: `tmp/variable-overlap/source-voter-scopes-full-build.log`.
  [Open voter/election application](docs/research/helios-source-voter-application.md)
  now certifies substitution of arbitrary valid ground candidates into one fixed
  open election under all scopes. Active domains remain variables; the key export,
  real administration and full policy are retained. A common fresh allocation
  supports both worlds. Every certified instance has the initial source path,
  action iff interfaces, frame/WF/static witnesses and a private communication.
  Twenty-three controls cover key/vote separation, local/name capture, full proof
  fields and outer-key freshness. Initial open-parameter application is discharged.
  Preceding board input/guard continuation syntax, independent frame compatibility,
  canonical environment/body correspondence and remaining admissibility/action
  matching stay open. B9/B10 remain unchecked at 8/10 milestones.
  Integrated `lake build`: 3959 jobs; 3738 standard-only and 68 axiom-free
  reports; 2820 theorem entries/108 documents; ten current oleans, 1340 local
  links; no proof holes/custom axioms/warnings/errors in the checked scope;
  diff check passes. Added 69 theorem audits and twenty-three controls; fifteen
  construction/substitution/instantiation definitions checked.
  Log: `tmp/variable-overlap/source-voter-application-full-build.log`.
  [Guarded board construction](docs/research/helios-source-guarded-board.md) now
  retains the explicit tally lets beneath the complete input/relay/guard chain.
  Exact substitution preserves input/local binders; actual source actions expose
  head lets and reject to null. Last acceptance activates the full tally block.
  The compiled whole board/election has full-E congruence and two-way evaluated
  action matching, with twenty kernel controls. This construction convention
  adds no structural rule beneath prefixes. General Named correspondence,
  independent frame compatibility, canonical environment/body correspondence
  and remaining admissibility/action matching stay open. B9/B10 remain unchecked
  at 8/10 milestones.
  Integrated verification: `lake build` passes **3966 jobs**. The log reports
  **3795** nonempty standard-only and **72** axiom-free results. The claim audit
  covers **2881** public theorem entries and **109** current-status documents.
  All nine changed Lean sources have current oleans; **1366** local links resolve.
  No proof holes, custom axioms, warnings or errors were found in the checked
  scope; `git diff --check` passes. This increment adds **61** theorem audits,
  including **20** public kernel controls, and checks eleven construction and
  substitution definitions. The targeted control build passes **1315 jobs**.
  Build log: `tmp/variable-overlap/source-guarded-board-full-build.log`.
  Freshness/hole/link evidence:
  `tmp/variable-overlap/source-guarded-board-verification.txt`.
  [Independent frame compatibility](docs/research/helios-source-frame-compatibility.md)
  now proves equality-test agreement for unrelated presentations of the same
  actual source frame and discharges Named.StaticEq transitivity via common-policy
  alignment. Every Named structural rule preserves the new frame constraints;
  universal validity is exactly canonical public recipe equality. Presentation
  witnesses supply nonvacuity. All literal tests transfer after freshening, actual
  internal/free actions preserve equations and output preserves old-handle tests.
  Twenty-three controls include atom collisions, alpha, inconsistent constraints,
  public-value separation and an actual old/new-handle publication. Canonical
  environment/body correspondence and general admissibility/action matching
  remain open. B9/B10 stay unchecked at 8/10 milestones.
  Integrated verification: `lake build` passes **3973 jobs**. The log reports
  **3857** nonempty standard-only and **72** axiom-free results. The claim audit
  covers **2943** public theorem entries and **110** current-status documents.
  All nine changed Lean sources have current oleans; **1388** local links resolve.
  No proof holes, custom axioms, warnings or errors were found in the checked
  scope; `git diff --check` passes. This increment adds **62** theorem audits,
  including **23** public kernel controls, and checks all three new constraint/
  observation definitions. The targeted control build passes **1313 jobs**.
  Build log: `tmp/variable-overlap/source-frame-compatibility-full-build.log`.
  Freshness/hole/link evidence:
  `tmp/variable-overlap/source-frame-compatibility-verification.txt`.
  Full Named body interpretation increment (2026-09-12): **machine-checked**
  Named.Structural.interprets for every current rule, plus exact canonical and
  prenex frame/body characterization under one assignment of both name sorts.
  Canonical states supply their literal environment/body and actual structural
  representatives retain it. Nineteen controls cover full fields, alpha, local
  and future inputs, election instances, stale exports and name collisions.
  Collisions can change guards or create communication; arbitrary interpretation
  witnesses do not establish action correspondence. Fresh/injective assignment
  selection, remaining admissibility/action matching and final source weak
  labelled bisimilarity/secrecy stay open. Independent frame compatibility and
  Named.StaticEq.trans remain proved. B9/B10 stay at 8/10 unweighted milestones.
  See [the body record](docs/research/helios-source-named-body.md).

  Integrated verification: `lake build` passes **3979 jobs**. The log reports
  **3899** nonempty standard-only and **74** axiom-free results. The claim audit
  covers **2987** public theorem entries and **111** current-status documents.
  All eight changed Lean sources have current oleans; **1420** local links resolve.
  No proof holes, custom axioms, warnings or errors were found in the checked
  scope; `git diff --check` passes. This increment adds **44** theorem audits,
  including **19** public kernel controls, and checks five assignment/interpretation
  definitions. The targeted control build passes **1313 jobs**.
  Build log: `tmp/variable-overlap/source-named-body-full-build.log`.
  Freshness/hole/link evidence:
  `tmp/variable-overlap/source-named-body-verification.txt`.

  Full Named visible increment (2026-09-12): **machine-checked** unrestricted
  forward FreeStep/BoundOutput interpretation, canonical scoped actions,
  common-fresh-policy input with retained old frame presentation, and exact
  election input/publication/stage/continuation classification. Actual outputs
  retain their complete message and old/new environments before/after handle
  renaming. Finite endpoint injectivity suffices for internal Extended reduction
  transport/reflection via Mathlib permutation extension. Twenty-two controls
  include real publications, rejected elections and refutations of global or
  finite-support injectivity at a fixed old environment after alpha/dead-field
  rewriting. General Named internal correspondence, required new-frame
  presentation/relation invariants and final source bisimilarity/secrecy remain
  open. B9/B10 stay at 8/10 unweighted milestones (80%).
  See [the Named visible record](docs/research/helios-source-named-visible.md).

  Integrated verification: `lake build` passes **3984 jobs**. The log reports
  **3942** nonempty standard-only and **74** axiom-free results. The claim audit
  covers **3030** public theorem entries and **112** current-status documents.
  All seven changed Lean sources have current oleans; **1434** local links resolve.
  No proof holes, custom axioms, warnings or errors were found in the checked
  scope; `git diff --check` passes. This increment adds **43** theorem audits,
  including **22** public kernel controls, and checks the finite-faithfulness
  definition. The targeted control build passes **1337 jobs**.
  Build log: `tmp/variable-overlap/source-named-visible-full-build.log`.
  Freshness/hole/link evidence:
  `tmp/variable-overlap/source-named-visible-verification.txt`.

  Named communication increment (2026-09-12): **machine-checked** exact
  classification/erasure of all original internal derivations; arbitrary-map
  forward communication through every Named context; actual either-world
  election communication matching with Named.StaticEq of raw targets and full
  continuation interpretation. The matching target uses the old frame and next
  body. Twenty-one controls include actual private voter/trustee delivery,
  noninjective forward transport, rejected elections and retained guard
  collision. General Named conditional correspondence, required target
  presentation/relation invariants and final source bisimilarity/secrecy remain
  open. B9/B10 stay at 8/10 unweighted milestones (80%). See
  [the communication record](docs/research/helios-source-communication.md).

  Integrated verification: `lake build` passes **3990 jobs**. The log reports
  **3989** nonempty standard-only and **75** axiom-free results. The claim audit
  covers **3078** public theorem entries and **113** current-status documents.
  All eight changed Lean sources have current oleans; **1458** local links resolve.
  No proof holes, custom axioms, warnings or errors were found in the checked
  scope; `git diff --check` passes. This increment adds **48** theorem audits,
  including **21** public kernel controls, and checks the three classified-derivation types. The targeted control build passes **1362 jobs**.
  Build log: `tmp/variable-overlap/source-communication-full-build.log`.
  Freshness/hole/link evidence:
  `tmp/variable-overlap/source-communication-verification.txt`.

  Conditional-location increment (2026-09-12): **machine-checked** ready-guard
  invariance under every interpretation context and exact check-phase location.
  Arbitrary original Named reductions from all non-check reached phases now
  match in either voting world, with actual target static equivalence and full
  continuation interpretation; communication is derived, not assumed. Quiet
  input/publication/rejected/completed phases exclude arbitrary internal targets
  through arbitrary structural source representatives. Nineteen controls retain
  actual accepting/rejecting checks and the explicit non-check boundary.
  Check-phase truth correspondence, required target presentation/relation
  invariants and final source bisimilarity/secrecy remain open. B9/B10 stay at
  8/10 unweighted milestones (80%). See
  [the conditional-location record](docs/research/helios-source-conditional-location.md).

  Integrated verification: `lake build` passes **3995 jobs**. The log reports
  **4032** nonempty standard-only and **76** axiom-free results. The claim audit
  covers **3122** public theorem entries and **114** current-status documents.
  All seven changed Lean sources have current oleans; **1470** local links resolve.
  No proof holes, custom axioms, warnings or errors were found in the checked
  scope; `git diff --check` passes. This increment adds **44** theorem audits,
  including **19** public kernel controls, and checks the readiness definition. The targeted control build passes **1367 jobs**.
  Build log: `tmp/variable-overlap/source-conditional-location-full-build.log`.
  Freshness/hole/link evidence:
  `tmp/variable-overlap/source-conditional-location-verification.txt`.

  Guard-retraction increment (2026-09-12): **machine-checked** recovery of
  complete terms/formulas modulo full E, both guard outcomes, ready-guard
  internal transport with complete mapped targets, substitution/environment
  compatibility and the full election proof/tail/replay guard. Twenty-one
  controls show that unused-field recovery works without literal injectivity,
  while essential-name and unrecovered SPK/ciphertext fields still fail.
  Actual true/false conditionals, Extended targets and an election replay check
  are retained. Selecting coherent witnesses through arbitrary Named check
  paths, target presentation/relation invariants and final source secrecy
  remain open. B9/B10 stay at 8/10 unweighted milestones (80%). See
  [the guard-retraction record](docs/research/helios-source-guard-retractions.md).

  Integrated verification: `lake build` passes **4001 jobs**. The log reports
  **4079** nonempty standard-only and **79** axiom-free results. The claim audit
  covers **3172** public theorem entries and **115** current-status documents.
  All eight changed Lean sources have current oleans; **1473** local links resolve.
  No proof holes, custom axioms, warnings or errors were found in the checked
  scope; `git diff --check` passes. This increment adds **50** theorem audits,
  including **21** public kernel controls, and checks the three recovery definitions. The targeted control build passes **1373 jobs**.
  Build log: `tmp/variable-overlap/source-guard-retraction-full-build.log`.
  Freshness/hole/link evidence:
  `tmp/variable-overlap/source-guard-retraction-verification.txt`.

  Fresh-opening increment (2026-09-12): **machine-checked** distinct
  scope-respecting allocations, arbitrary finite avoidance, complete body support
  and interpretation reconstruction. Sufficiently fresh chosen openings have
  actual Structural derivations. Canonical openings construct complete frame/
  body permutations, literal realizations and guard-recovery witnesses without
  assuming them. Eighteen controls cover full payloads, shadowing, parallel
  binders, variable constraints and the free-capture boundary. Comparison across
  arbitrary structural/action paths, Named check correspondence, target/relation
  invariants and final secrecy remain open. B9/B10 stay at 8/10 unweighted
  milestones (80%). See [the opening record](docs/research/helios-source-openings.md).

  Integrated verification: `lake build` passes **4008 jobs**. The log reports
  **4121** nonempty standard-only and **83** axiom-free results. The claim audit
  covers **3218** public theorem entries and **116** current-status documents.
  All nine changed Lean sources have current oleans; **1487** local links resolve.
  No proof holes, custom axioms, warnings or errors were found in the checked
  scope; `git diff --check` passes. This increment adds **46** theorem audits,
  including **18** public kernel controls, and checks the three opening definitions. The targeted control build passes **1380 jobs**.
  Build log: `tmp/variable-overlap/source-opening-full-build.log`.
  Freshness/hole/link evidence:
  `tmp/variable-overlap/source-opening-verification.txt`.

  Opening-comparison increment (2026-09-12): **machine-checked** every
  Named Structural rule transports fresh openings with equality of all full
  realizations and arbitrary finite avoidance. Actual Named internal reductions
  derive sufficient avoidance, yielding actual canonical Tau and full raw-target
  interpretation in coherent fresh coordinates. Reached canonical representatives
  now have actual one-step matching in either vote world, including check
  branches, and target StaticEq. Twenty-three controls retain both guard outcomes,
  all constraints, capture boundaries and quiet-process exclusion. Target/relation
  closure, policy/coordinate invariants, output-frame presentation and final
  secrecy remain open. B9/B10 stay at 8/10 unweighted milestones (80%). See
  [the comparison record](docs/research/helios-source-opening-comparison.md).

  Integrated verification: `lake build` passes **4020 jobs**. The log reports
  **4189** nonempty standard-only and **85** axiom-free results. The claim audit
  covers **3288** public theorem entries and **117** current-status documents.
  All fourteen changed Lean sources have current oleans; **1498** local links
  resolve. No proof holes, custom axioms, warnings or errors were found in the
  checked scope; `git diff --check` passes. This increment adds **70** theorem
  audits, including **23** public kernel controls, and checks three comparison
  definitions. The targeted control build passes **1392 jobs**.
  Build log: `tmp/variable-overlap/source-opening-comparison-full-build.log`.
  Freshness/hole/link evidence:
  `tmp/variable-overlap/source-opening-comparison-verification.txt`.

  Full-target-invariant increment (2026-09-12): **machine-checked**
  backward full realization, deterministic all-environment target-class closure,
  paired actual opening actions and refresh fixing free source names.
  HasCanonicalOpening is internally preserved on arbitrary raw targets; exact
  next-frame identity and handle transport give PhaseOpening, retained by every
  finite actual internal source sequence. Twenty-seven controls include both
  branches, full constraints/payloads, nondeterminism and two actual trustee
  steps. Action construction from arbitrary invariant representatives, visible
  closure, output-frame/public-policy invariants and final secrecy remain open.
  B9/B10 stay at 8/10 unweighted milestones (80%). See
  [the target-invariant record](docs/research/helios-source-target-invariant.md).

  Integrated verification: `lake build` passes **4030 jobs**. The log reports
  **4247** nonempty standard-only and **86** axiom-free results. The claim audit
  covers **3347** public theorem entries and **118** current-status documents.
  All twelve changed Lean sources have current oleans; **1517** local links
  resolve. No proof holes, custom axioms, warnings or errors were found in the
  checked scope; `git diff --check` passes. This increment adds **59** theorem
  audits, including **27** public kernel controls, and checks three new definitions.
  The targeted control build passes **1402 jobs**.
  Build log: `tmp/variable-overlap/source-target-invariant-full-build.log`.
  Freshness/hole/link evidence:
  `tmp/variable-overlap/source-target-invariant-verification.txt`.

  Visible-invariant increment (2026-09-12): **machine-checked** backward
  visible realization, complete input/fresh-output target classes, paired actual
  opening actions and HasCanonicalOpening preservation under input/bound output.
  All election residuals have full visible determinism. Twenty-nine controls
  retain complete SPK/old/fresh values, Scope and actual Named actions.
  **Refuted:** the body invariant alone preserves restriction policy; public and
  restricted outputs share it but differ in visibility. Restriction/policy and
  label/phase alignment, arbitrary-representative action construction, existing-
  handle output closure, output-frame presentation and final secrecy remain open.
  B9/B10 stay at 8/10 unweighted milestones (80%). See
  [the visible-invariant record](docs/research/helios-source-visible-invariant.md).

  Integrated verification: `lake build` passes **4039 jobs**. The log reports
  **4294** nonempty standard-only and **90** axiom-free results. The claim audit
  covers **3398** public theorem entries and **119** current-status documents.
  All eleven changed Lean sources have current oleans; **1534** local links
  resolve. No proof holes, custom axioms, warnings or errors were found in the
  checked scope; `git diff --check` passes. This increment adds **51** theorem
  audits, including **29** public kernel controls, and no production definitions.
  The targeted control build passes **1411 jobs**.
  Build log: `tmp/variable-overlap/source-visible-invariant-full-build.log`.
  Freshness/hole/link evidence:
  `tmp/variable-overlap/source-visible-invariant-verification.txt`.

  Joint-opening increment (2026-09-12): **machine-checked** coherent fresh
  openings of both actual scoped processes, all-Structural preservation, full
  nonempty realization equality and free-channel preservation. Canonical
  partners supply the prior body invariant and block actual private-channel
  actions. Sixteen controls accept alpha/unused restrictions, reject the old
  private/public pair and expose empty-class vacuity. Operational closure of
  the stronger relation, input-recipe/phase alignment, action construction,
  output closure/frame presentation and final secrecy remain open. B9/B10 stay
  at 8/10 unweighted milestones (80%). See
  [joint fresh openings](docs/research/helios-source-joint-openings.md).

  Integrated verification: `lake build` passes **4043 jobs**. The log reports
  **4329** nonempty standard-only and **90** axiom-free results. The claim audit
  covers **3433** public theorem entries and **120** current-status documents.
  All six changed Lean sources have current oleans; **1545** local links resolve.
  No proof holes, custom axioms, warnings or errors were found in the checked
  scope; `git diff --check` passes. This increment adds **35** theorem audits,
  including **16** public kernel controls, and one candidate relation definition.
  The targeted control build passes **1415 jobs**.
  Build log: `tmp/variable-overlap/source-joint-opening-full-build.log`.
  Freshness/hole/link evidence:
  `tmp/variable-overlap/source-joint-opening-verification.txt`.

  Joint-internal increment (2026-09-12): **machine-checked** actual raw
  internal steps preserve the joint relation with the restricted canonical
  frame/body. Paired permutations cover both endpoint supports. Election
  determinism and exact state/domain transport yield PhaseJointOpening and
  preservation along every finite raw internal trace from a reached phase.
  Nineteen controls include a two-step trustee trace, full-SPK private
  communication, structural targets and private-channel blocking after
  arbitrary internal traces. Joint visible closure, input-recipe/phase
  alignment, action construction, output closure/frame presentation and final
  secrecy remain open. B9/B10 stay at 8/10 unweighted milestones (80%). See
  [joint internal closure](docs/research/helios-source-joint-internal.md).

  Integrated verification: `lake build` passes **4047 jobs**. The log reports
  **4360** nonempty standard-only and **91** axiom-free results. The claim audit
  covers **3465** public theorem entries and **121** current-status documents.
  All six changed Lean sources have current oleans; **1555** local links resolve.
  No proof holes, custom axioms, warnings or errors were found in the checked
  scope; `git diff --check` passes. This increment adds **32** theorem audits,
  including **19** public kernel controls, and one phase invariant definition.
  The targeted control build passes **1419 jobs**.
  Build log: `tmp/variable-overlap/source-joint-internal-full-build.log`.
  Freshness/hole/link evidence:
  `tmp/variable-overlap/source-joint-internal-verification.txt`.

  Joint-visible increment (2026-09-12): **machine-checked** public input
  and full bound-output target closure with exact raw channels and actual
  restrictions. Arbitrary input recipes become public under a common derived
  fresh policy in both worlds, preserving old-frame StaticEq and the full raw
  target relation. Actual outputs identify Publication/next PhaseJointOpening
  with exact new handle domain. Twenty-two controls include the alpha-input
  boundary and first-publication closure. Input-phase matching across fresh
  coordinates, arbitrary action construction, existing-handle output closure,
  output-frame presentation and final secrecy remain open. B9/B10 stay at
  8/10 unweighted milestones (80%). See
  [joint visible closure](docs/research/helios-source-joint-visible.md).

  Integrated verification: `lake build` passes **4053 jobs**. The log reports
  **4397** nonempty standard-only and **91** axiom-free results. The claim audit
  covers **3502** public theorem entries and **122** current-status documents.
  All eight changed Lean sources have current oleans; **1565** local links resolve.
  No proof holes, custom axioms, warnings or errors were found in the checked
  scope; `git diff --check` passes. This increment adds **37** theorem audits,
  including **22** public kernel controls, and no production definitions.
  The targeted control build passes **1424 jobs**.
  Build log: `tmp/variable-overlap/source-joint-visible-full-build.log`.
  Freshness/hole/link evidence:
  `tmp/variable-overlap/source-joint-visible-verification.txt`.

  Coordinated-phase increment (2026-09-12): **machine-checked** shared
  canonical name coordinates, arbitrary-input check-phase matching after common
  freshening, full raw target closure and an actual same-label input from the
  other fresh canonical partner. Subsequent internal traces and bound outputs
  retain current coordinates and exact full next states/domains. Twenty controls
  cover nonidentity coordinates, old private literals, composition order,
  real input/internal/output actions and private blocking. Arbitrary raw partner
  action construction, existing-handle output closure, raw output-frame
  presentation and final secrecy remain open. B9/B10 stay at 8/10 unweighted
  milestones (80%). See
  [coordinated phases](docs/research/helios-source-coordinated-phases.md).

  Integrated verification: `lake build` passes **4060 jobs**. The log reports
  **4434** nonempty standard-only and **91** axiom-free results. The claim audit
  covers **3539** public theorem entries and **123** current-status documents.
  All nine changed Lean sources have current oleans; **1578** local links resolve.
  No proof holes, custom axioms, warnings or errors were found in the checked
  scope; `git diff --check` passes. This increment adds **37** theorem audits,
  including **20** public kernel controls, and two proof definitions.
  The targeted control build passes **1431 jobs**.
  Build log: `tmp/variable-overlap/source-coordinated-full-build.log`.
  Freshness/hole/link evidence:
  `tmp/variable-overlap/source-coordinated-verification.txt`.

  Existing-handle output increment: generic full target-class and joint-opening
  closure are machine-checked, with the old domain, all old values, actual name
  restrictions and literal public channel retained. Determinism is restricted
  to continuations emitting an E-equal handle value. Canonical Out-Atom actions
  are derived from the original Subst/Scope rules. Twelve controls include full
  SPKs differing only in their fourth field, wrong handle labels for all raw
  targets, changed emitted/unemitted values, E-equivalent environments,
  noncanonical endpoints and private blocking.
  Integrated verification: `lake build` passes **4064 jobs**. The current log
  reports **4453** nonempty standard-only and **91** axiom-free results. The claim
  audit covers **3558** public theorem entries and **124** current-status documents.
  All six changed Lean sources have current oleans; **1601** local links resolve.
  No proof holes, custom axioms, warnings or errors were found in the checked
  scope; `git diff --check` passes. This increment adds **19** theorem audits,
  including **12** public kernel controls, and no production definitions.
  The targeted control build passes **1420 jobs**.
  Build log: `tmp/variable-overlap/source-handle-output-full-build.log`.
  Freshness/hole/link evidence:
  `tmp/variable-overlap/source-handle-output-verification.txt`.
  Election-level old-domain treatment, arbitrary raw matching, raw bound-output
  frame presentation and final secrecy remain open; B9/B10 stay unchecked at
  8/10 milestones (80%, unweighted). See
  [the output record](docs/research/helios-source-handle-output.md).

  Election existing-handle case: closed by machine-checked exclusion. Every
  actual publication in a reached fresh election differs modulo full E from
  every old handle. Arbitrary jointly related raw representatives, including
  current name coordinates and domain casts, therefore have no old-handle free
  output on any channel to any target. Thirteen controls retain all four live
  bound publications, exercise noncanonical endpoints, and expose nonce
  freshness with a whole-ballot collision and an allowed Out-Atom prefix.
  Integrated verification: `lake build` passes **4067 jobs**. The current log
  reports **4474** nonempty standard-only and **91** axiom-free results. The claim
  audit covers **3579** public theorem entries and **125** current-status documents.
  All five changed Lean sources have current oleans; **1620** local links resolve.
  No proof holes, custom axioms, warnings or errors were found in the checked
  scope; `git diff --check` passes. This increment adds **21** theorem audits,
  including **13** public kernel controls, and no production definitions.
  The targeted control build passes **1437 jobs**.
  Build log: `tmp/variable-overlap/source-election-handle-full-build.log`.
  Freshness/hole/link evidence:
  `tmp/variable-overlap/source-election-handle-verification.txt`.
  Arbitrary raw matching, raw bound-output Structural frame presentation and
  final secrecy remain open; B9/B10 stay unchecked at 8/10 milestones (80%,
  unweighted). See [publication separation](docs/research/helios-source-publication-separation.md).

  Reconstruction enquiry: the Extended normalization implication from
  WellFormed, nonempty full SameRealizations alone is kernel-refuted. The local
  self-reference νx.{x/x} has nil's class but two E-distinct solutions. New
  local rigidity is invariant under all original Extended structural/internal/
  free rules; canonical frames are rigid. The counterexample persists beside
  any complete public frame/body and also admits the embedded joint relation.
  Thirteen controls retain real Alias normalization, conditional progress and
  actual public input beside the cycle. No Named.Structural separation or
  action-matching counterexample is claimed.
  Integrated verification: `lake build` passes **4071 jobs**. The current log
  reports **4504** nonempty standard-only and **91** axiom-free results. The claim
  audit covers **3609** public theorem entries and **126** current-status documents.
  All six changed Lean sources have current oleans; **1624** local links resolve.
  No proof holes, custom axioms, warnings or errors were found in the checked
  scope; `git diff --check` passes. This increment adds **30** theorem audits,
  including **13** public kernel controls, and one auxiliary proof definition.
  The targeted control build passes **1210 jobs**.
  Build log: `tmp/variable-overlap/source-local-rigidity-full-build.log`.
  Freshness/hole/link evidence:
  `tmp/variable-overlap/source-local-rigidity-verification.txt`.
  Rigidity is necessary, not proved sufficient. Named/bound-output preservation,
  stronger reachable reconstruction, raw matching/frame presentation and final
  secrecy remain open; B9/B10 stay unchecked at 8/10 unweighted milestones.
  See [local rigidity](docs/research/helios-source-local-rigidity.md).

  Binder/presentation increment: variable commutation and Extended bound output
  preserve rigidity; frame reclosure preserves it exactly. Existing name-opening
  comparison now returns actual BinderStructural witnesses, which map to the
  original Named.Structural rules; the old semantic transport API remains.
  Every frame presentation forces all openings rigid. The cyclic joint pair
  therefore has no full Named normalization or ground presentation under any
  policy/values, and no Named.StaticEq partner. Seventeen controls retain real
  dependent/scoped output behavior and canonical static observations; a real
  unconstrained export refutes converse rigidity preservation.
  Integrated verification: `lake build` passes **4078 jobs**; the targeted controls
  pass **1370 jobs**. The current log reports **4546** nonempty standard-only and
  **91** axiom-free results. The claim audit covers **3651** public theorem entries
  and **127** current-status documents. All fourteen changed Lean sources have
  current oleans; **1627** local links resolve. No proof holes, custom axioms,
  warnings or errors were found in the checked scope; `git diff --check` passes.
  This increment adds **42** theorem audits, including **17** public kernel
  controls, and one auxiliary comparison definition. Existing opening comparisons
  are strengthened in place; the previous semantic transport interface and its
  avoidance control remain checked.
  Log: `tmp/variable-overlap/source-binder-rigidity-full-build.log`.
  Rigidity sufficiency, maintained Named action integration, reachable raw
  reconstruction/matching, bound-output frame presentation and final secrecy
  remain open; B9/B10 stay unchecked at 8/10 unweighted milestones.
  See [binder rigidity](docs/research/helios-source-binder-rigidity.md).

  **Named execution-rigidity evidence (2026-09-12):** All actual name openings
  and complete environments retain local-solution rigidity through every
  original Named structural/internal/free rule and forward through bound
  output; reclosure is exact. Bijective handle relabelling is proved. Finite
  Execution closes those original derivations and explicit coordinate changes,
  so every presented/canonical starting state excludes the cyclic joint family
  at every target, including mapped canonical election phases. This adds no
  operational rule or matching premise. Twenty controls retain real scoped
  output then input, distinct local/capture values, canonical publication across
  Option/Fin domains, private communication and a counterexample to reverse
  output preservation.
  Integrated verification: `lake build` passes **4081 jobs**; targeted controls
  pass **1397 jobs**. The current log reports **4588** nonempty standard-only and
  **91** axiom-free results. The claim audit covers **3693** public theorem entries
  and **128** current-status documents. All five changed Lean sources have current
  oleans; **1649** local links resolve. No proof holes, custom axioms, warnings or
  errors were found in the checked scope; `git diff --check` passes. This increment
  adds **42** theorem audits, including **20** public kernel controls, and two
  auxiliary definitions (LocallyRigid and the original-action execution closure).
  Log: `tmp/variable-overlap/source-rigid-execution-full-build.log`.
  Necessary Named action rigidity is closed; sufficient reachable reconstruction,
  arbitrary raw matching, raw bound-output frame presentation and final secrecy
  remain open. B9/B10 stay unchecked at 8/10 unweighted milestones. See
  [Named execution rigidity](docs/research/helios-source-rigid-execution.md).

  **Recipe-capture reconstruction evidence (2026-09-12):** A finite ground
  provider frame now instantiates arbitrary disjoint Extended contexts while
  retaining exact syntax and an original Structural path. Shifted canonical
  providers preserve fresh None and ground every old handle. An explicit fresh
  old-handle-recipe capture and arbitrary plain continuation now reconstruct
  the complete extended frame under outputHandle; the same sorted prefix gives
  actual Named ground-frame presentations. Real Extended/Named non-ground
  outputs include full reconstructed targets. Eighteen controls retain nested
  input/local binders, all old/new values and the full SPK fourth field, and
  reject changed captures plus omitted/redefined providers.
  Integrated verification: `lake build` passes **4084 jobs**; targeted controls
  pass **1148 jobs**. The current log reports **4618** nonempty standard-only and
  **91** axiom-free results. The claim audit covers **3723** public theorem entries
  and **129** current-status documents. All five changed Lean sources have current
  oleans; **1661** local links resolve. No proof holes, custom axioms, warnings or
  errors were found in the checked scope; `git diff --check` passes. This increment
  adds **30** theorem audits, including **18** public kernel controls, with no new
  production definition or operational rule.
  Log: `tmp/variable-overlap/source-recipe-capture-full-build.log`.
  General extraction of that syntax class through reachable structural detours,
  arbitrary raw matching, general bound-output frame presentation and final
  secrecy remain open. B9/B10 stay unchecked at 8/10 unweighted milestones. See
  [recipe capture reconstruction](docs/research/helios-source-recipe-capture.md).

  **Dependent program-capture evidence (2026-09-12):** Original Scope now
  derives the actual retained-local output target of every finite existing
  TermProgram. Subst/Alias eliminates its dependent locals into the full
  computed capture. The general single-scope lemma retains arbitrary plain
  continuations and future input binders. Full old-frame and Named ground-frame
  presentation/output reconstruction follow under the original sorted prefix.
  Twenty-one controls retain two dependent locals, literal exchanged binder
  positions, full values, three final handles, actual static observations and
  same-input progress, rejecting wrong values and merged capture domains.
  Integrated verification: `lake build` passes **4087 jobs**; targeted controls
  pass **1152 jobs**. The current log reports **4648** nonempty standard-only and
  **92** axiom-free results. The claim audit covers **3754** public theorem entries
  and **130** current-status documents. All five changed Lean sources have current
  oleans; **1683** local links resolve. No proof holes, custom axioms, warnings or
  errors were found in the checked scope; `git diff --check` passes. This increment
  adds **31** theorem audits, including **21** public kernel controls, and one raw
  target definition (TermProgram.capture), with no new program datatype or
  operational rule.
  Log: `tmp/variable-overlap/source-program-capture-full-build.log`.
  General extraction through reachable structural detours, arbitrary interleaved
  name scopes, general raw matching/output frame presentation and final secrecy
  remain open. B9/B10 stay unchecked at 8/10 unweighted milestones. See
  [dependent program captures](docs/research/helios-source-program-capture.md).

  **Scoped program-capture evidence (2026-09-12):** Original Named output
  retains every interleaved ScopedTermProgram base-name/local scope, with no
  hoisting premise. Hoistable and freshness for every old frame value then
  give actual full frame reconstruction at restricted union program.names.
  Existing source prefix reordering/dedup supports repeated names. Twenty-two
  controls retain literal scope positions, complete values/private policy,
  actual static observations, failed-hoisting outputs, repeated restrictions
  and distinct base/channel sorts. No source rule or program type is added.
  Integrated verification: `lake build` passes **4090 jobs**; targeted controls
  pass **1166 jobs**. The current log reports **4678** nonempty standard-only and
  **92** axiom-free results. The claim audit covers **3784** public theorem entries
  and **131** current-status documents. All five changed Lean sources have current
  oleans; **1675** local links resolve. No proof holes, custom axioms, warnings or
  errors were found in the checked scope; `git diff --check` passes. This increment
  adds **30** theorem audits, including **22** public kernel controls, and one raw
  target definition (ScopedTermProgram.capture), with no new program datatype or
  operational rule.
  Log: `tmp/variable-overlap/source-scoped-capture-full-build.log`.
  General extraction through reachable structural representatives, general raw
  matching/output frame presentation and final secrecy remain open. B9/B10
  stay unchecked at 8/10 unweighted milestones. See
  [scoped program captures](docs/research/helios-source-scoped-capture.md).

  **Structural opening evidence (2026-09-12):** All three paired action
  openings retain BinderStructural paths; original Named actions connect the
  embedded opened endpoints with full labels and fresh-variable targets.
  Jointly fresh binder-structural openings characterize actual Named structure,
  with unequal allocation lists handled by actual unused-name/prefix rules.
  Fifteen controls cover used names, dependent locals and real actions, and
  refute missing freshness or semantic-only reconstruction.
  Integrated verification: `lake build` passes **4093 jobs**; targeted controls
  pass **1394 jobs**. The current log reports **4703** nonempty standard-only and
  **92** axiom-free results. The claim audit covers **3809** public theorem entries
  and **132** current-status documents. All seven changed Lean sources have current
  oleans; **1686** local links resolve. No proof holes, custom axioms, warnings or
  errors were found in the checked scope; `git diff --check` passes. This increment
  adds **25** theorem audits, including **15** public kernel controls, with no new
  definition or operational rule.
  Log: `tmp/variable-overlap/source-structural-opening-full-build.log`.
  Deriving structural body evidence for arbitrary reachable raw targets,
  general matching/output-frame reconstruction and final secrecy remain open.
  B9/B10 stay unchecked at 8/10 milestones. See
  [structural action openings](docs/research/helios-source-structural-openings.md).

  **Closure priorities after source inspection (2026-09-12):** First compose
  the existing source successor classifications as Named.Execution.election_phase
  and scopedVoterElection_execution_phase, including input coordinate refresh
  and fresh-output handle bijections. Then prove source_reachable_frame_presentation
  for actual reachable targets; derive source_reachable_internal_match,
  source_reachable_input_match and source_reachable_bound_match from the actual
  raw partner with related successors. Assemble source_reachable_weak_bisimulation,
  source_election_weak_bisimilar and scopedVoterElection_ballot_secrecy only after
  those obligations are discharged. These are planned declarations, not assumed
  correspondence premises. Initial scoped-voter extraction/fresh allocation is
  already checked. Preserve the semantic-only counterexample. See the detailed
  dependency/status map in the existing [blueprint](docs/research/helios-proof-blueprint.md).
  Keep the retrospective reuse audit after secrecy; no framework migration or
  additional Lake dependency is authorized by this plan.

  **Reachable execution phase evidence (2026-09-12):** The planned
  Named.Execution.election_phase and scopedVoterElection_execution_phase are
  now checked for every original finite mixed execution. They retain reached
  phases, refreshed name coordinates and complete handle bijections, starting
  from the actual scoped source. exists_scoped_execution_phase discharges
  initial parameter/nonce freshness; the old-handle exclusion now applies to
  all actually reached raw states. Thirteen controls cover two publications,
  replay/rejection and handle reindexing. No new execution relation or rule.
  Integrated evidence: `lake build` succeeds (4096 jobs); the targeted control
  build succeeds (1454 jobs). The current full log contains 4727 standard-only
  nonempty and 92 axiom-free reports. The checker covers 3833 public theorem
  entries and 132 current-status documents. Five changed Lean oleans are current;
  1683 local links resolve. No holes, custom axioms, warnings or errors were found
  in scope; `git diff --check` passes. This increment adds 24 public theorem
  audits, including 13 controls, and no new definition or operational rule.
  Log: `tmp/variable-overlap/source-reachable-election-full-build.log`.
  NEXT remains source_reachable_frame_presentation, followed by the planned
  raw-partner matching and B10 declarations above. This closes phase tracking,
  not presentation, bisimilarity or secrecy. See the existing
  [coordinated-phase evidence](docs/research/helios-source-coordinated-phases.md).

  **Actual presentation branch evidence (2026-09-12):**
  source_coordinated_internal_presented_next and
  source_coordinated_input_presented_next now retain full actual presentations
  through internal steps and arbitrary inputs, assuming the current actual
  presentations as induction hypotheses. Input freshness and policy changes
  are derived from actual whole-state structural paths. The raw partner's
  presentation/joint witness is retained; its matching input remains open.
  A checked latent-private-output counterexample refutes obtaining same-policy
  output presentation from old-frame presentation and reclosure alone.
  Five input/internal and eight policy controls retain positive/negative cases.
  Integrated evidence: `lake build` succeeds (4098 jobs); targeted controls
  succeed (1458 jobs). The current log has 4745 standard-only nonempty and 92
  axiom-free reports. The checker covers 3851 public theorem entries and 132
  current-status documents. Five changed Lean oleans are current; 1684 local
  links resolve. No holes, custom axioms, warnings or errors were found in scope;
  `git diff --check` passes. This increment adds 18 public theorem audits,
  including 13 controls, with no new operational rule or execution relation.
  Log: `tmp/variable-overlap/source-input-presentation-full-build.log`.
  NEXT: constructive fresh-output presentation with actual full process/phase
  provenance, then raw-partner matching and B10. Keep the existing cyclic
  semantic counterexample. See [actual closure evidence](docs/research/helios-source-coordinated-phases.md).

  Policy/value alignment is now machine-checked and integrated in
  SourcePresentationAlignment: JointOpening.align_presentation recovers the
  prescribed full canonical frame from a joint witness and some actual target
  presentation. Both opened frames have actual BinderStructural evidence before
  their equations are compared. SourcePresentationAlignmentSPOT's five controls
  retain the inhabited cyclic and output-policy counterexamples and exercise
  actual private capture with a larger initial presentation policy.
  Next: conjectured Named.BoundOutput.exists_frame_presentation must construct
  that existential target presentation from the actual output/current frame,
  preserving dependent local providers and all Option/outputHandle coordinates.
  Then apply alignment to source_coordinated_output_next's full phase witness
  and finish source_reachable_frame_presentation. Raw-partner internal/input/
  bound matching and B10 bisimilarity/secrecy remain open; no B9/B10 box changes.
  Existing scoped-program capture does not discharge arbitrary extraction.
  See [the current source record](docs/research/helios-source-coordinated-phases.md)
  and [blueprint](docs/research/helios-proof-blueprint.md).

  Integrated evidence: `lake build` succeeds (4100 jobs), including all five
  new controls. The clean targeted control build succeeds (1403 jobs). The current
  full log contains 4757 standard-only nonempty and 92 axiom-free reports; the
  claims checker covers 3863 public theorem entries and 132 current-status
  documents. Four changed Lean oleans are current, and all 1684 local links resolve.
  No holes, custom axioms, warnings or errors were found in scope; `git diff
  --check` passes. Twelve public theorem audits were added. No operational rule,
  execution relation or cryptographic assumption was added.
  Log: `tmp/variable-overlap/source-presentation-alignment-full-build.log`.

  Reachable finite-provider extraction is now machine-checked and integrated.
  SourceVariableFramePrefix derives an actual fresh name/variable-prefix frame
  path and exactly one provider for every local/public slot. The universal
  normal form retains all equations, including cyclic ones; it is not a ground
  presentation. SourceReachableFramePrefix proves complete definitions through
  every original execution and derives the full forest directly from the actual
  scoped election, together with the reached phase and exact handle bijection.
  No caller-supplied current presentation or program extraction is needed there.
  Seven controls include dependent locals, fresh/public coordinate separation,
  the preserved cycle, actual private output and actual historical rejection.
  Next: Named.BoundOutput.exists_frame_presentation must derive ground elimination
  from actual source presentation/output provenance. Then use checked phase
  alignment, close source_reachable_frame_presentation and actual raw-partner
  matching, and assemble/audit B10. All B9/B10 items remain unchecked.
  See [current extraction evidence](docs/research/helios-source-coordinated-phases.md)
  and [blueprint dependencies](docs/research/helios-proof-blueprint.md).

  Integrated evidence: `lake build` succeeds (4103 jobs); the clean targeted
  control build succeeds (1461 jobs). The current full log contains 4773
  standard-only nonempty and 101 axiom-free reports. The claims checker covers
  3883 public theorem entries and 132 current-status documents. Five changed Lean
  oleans are current, and 1684 local links resolve. No holes, custom axioms,
  warnings or errors were found in scope; `git diff --check` passes. Twenty public
  theorem audits, seven controls and five definition checks were added. The new
  definitions describe variable-prefix notation and a frame-syntax predicate;
  no operational rule or execution relation was added.
  Log: `tmp/variable-overlap/source-variable-frame-prefix-full-build.log`.

  Actual output algebraic values are now machine-checked and integrated.
  Named.BoundOutput.opened_algebra_values in SourceFrameAlgebra derives a ground witness,
  its original satisfying assignment, and every old/fresh value in every full-E
  algebra from the actual output and current presentation. Source structural
  provenance derives the necessary stronger uniqueness and ground witness. The
  universal clause requires a satisfying model environment, still to be built
  for the source-capture quotient. SourceFrameAlgebraQuotient supplies the
  term-congruence quotient constructor and a nontrivial original-E instance.
  Eleven controls retain both source values and the cyclic/name-opening boundaries.
  Next: prove actual fresh-capture Structural equality is a term congruence with
  provider equations, instantiate that quotient on the extracted complete forest,
  and derive the alias/copy and reclosure bridge. These remain conjectured parts
  of Named.BoundOutput.exists_frame_presentation; do not assume them. Then apply
  checked phase alignment, close reachable presentations and actual raw-partner
  matching, and assemble/audit B10. No B9/B10 completion box changes.
  See [current source evidence](docs/research/helios-source-coordinated-phases.md)
  and [the exact remaining dependencies](docs/research/helios-proof-blueprint.md).

  Integrated evidence: `lake build` succeeds (4106 jobs); the clean targeted
  control build succeeds (1408 jobs). The current full log contains 4820
  standard-only nonempty and 101 axiom-free reports. The claims checker covers
  3923 public theorem entries and 132 current-status documents. Five changed Lean
  oleans are current, and all 1684 local links resolve. No holes, custom axioms,
  warnings or errors were found in scope; `git diff --check` passes. Forty public
  theorem audits, eleven controls and seven definition checks were added. The
  algebra/quotient definitions are proof instrumentation, with no new source rule,
  execution relation or cryptographic assumption.
  Log: `tmp/variable-overlap/source-frame-algebra-full-build.log`.

  B9 reachable-state frame reconstruction is now machine-checked, integrated
  and audited. source_reachable_frame_presentation derives the exact phase,
  handle bijection and full actual RepresentsFrame witness for every finite
  original scoped-election execution. The output branch closes actual capture
  congruence, the derived quotient model, alias/copy identity, old-frame reclosure,
  full fresh-name policy extraction and checked phase alignment. Its only initial
  conditions are the actual source execution and documented parameter freshness.
  Both cyclic semantic and same-old-policy counterexamples remain. This completes
  the reconstruction obligation, not B9 action matching or B10 secrecy.

  Integrated evidence: `lake build` succeeds (4113 jobs); the clean targeted
  control build succeeds (1474 jobs). The current full log contains 4869
  standard-only nonempty and 103 axiom-free reports. The claims checker covers
  3969 public theorem entries and 132 current-status documents. Nine changed Lean
  oleans are current, and all 1684 local links resolve. No holes, custom axioms,
  warnings or errors were found in scope; `git diff --check` passes. Forty-six
  public theorem audits, fifteen controls and five definition checks were added.
  Log: `tmp/variable-overlap/source-reachable-frame-presentation-full-build.log`.

  Remaining B9/B10 acceptance obligations:

  1. **Open — actual raw-partner action availability.** Given the maintained
     reachable source relation and a corresponding evaluated phase action, derive
     a real action (or the required internal weak sequence) from the other raw
     source state. The new frame presentation theorem supplies observations and
     provider equations; it does not reconstruct live code or supply an action.
     Inspect existing realization/interpretation and canonical action derivations
     for the precise missing converse before adding machinery.
  2. **Open — source_reachable_internal_match, source_reachable_input_match and
     source_reachable_bound_match.** Use availability and existing phase matching
     to retain both actual successors in one relation. Preserve exact old/fresh
     handle domains, jointly refreshed private policies, unchanged public input
     recipes, output freshness, acceptance and stop-on-rejection behavior. The
     existing common-input result constructs a canonical partner action only.
  3. **Open — source_reachable_weak_bisimulation and
     source_election_weak_bisimilar.** Assemble symmetric internal/free/bound action
     clauses and actual Named.StaticEq observations after B9 acceptance closes.
  4. **Open — scopedVoterElection_ballot_secrecy.** Transfer the bisimulation to
     the actual scoped elections with documented freshness, arbitrary valid ground
     parameters and arbitrary finite administration size. Audit public hypotheses,
     full E/E0 observations and independently derived controls; no missing
     correspondence may become a final theorem premise.

  The retrospective reuse audit remains after B1–B10 secrecy completion.

  See [the maintained dependency map](docs/research/helios-proof-blueprint.md)
  and [integrated source evidence](docs/research/helios-source-coordinated-phases.md).

  Focused next action obligation after inspecting source rules: prove
  Named.JointOpening.input_available and Named.JointOpening.bound_available for
  an enabled public phase action, then use the existing coordinated target lemmas
  to classify the actual raw successors. These names are planned, not checked.
  SourceAtomicLabels.FreeStep.input and SourceAtomicOutput.message_output accept
  raw payload syntax, so input/output availability should need exposed source
  prefixes and fresh name openings rather than normalization of every live-code
  payload. SourceEvaluatedEquivalence preserves prefix behavior, and the existing
  Visible inversion/parallel lemmas expose those prefixes. Construct exact input
  recipes and fresh output coordinates through local and name scopes. Directed
  controls must include a ready public prefix, a prefix blocked underneath another
  input/output, and a private channel that cannot be exported as a public action.
  Internal communication then needs two compatible ready prefixes. Conditional
  availability separately requires the actual guard decision in its provider
  context; the existing forward conditional-location result does not prove it.
  This is the next concrete boundary to close before building a larger live-code
  normalization layer. No new source abstraction has been added for it.

  B9 raw-partner input and fresh-output matching are now machine-checked,
  integrated and audited. JointOpening.input_available/bound_available derive
  actual raw actions from ready public prefixes and fresh full name openings.
  source_reachable_input_match retains the unchanged recipe, jointly refreshed
  policies and both complete actual successor presentations/observations.
  source_reachable_bound_match retains the same channel and full fresh-handle
  bijection with statically equivalent actual successors. Both directions and
  nonidentity/private-literal coordinates are covered by checked controls.
  No canonical-only action or caller-supplied live-code normalization is assumed.

  Integrated evidence: `lake build` succeeds (4118 jobs); the clean targeted
  control build succeeds (1468 jobs). The current full log contains 4899
  standard-only nonempty and 103 axiom-free reports. The claims checker covers
  3997 public theorem entries and 132 current-status documents. Seven changed Lean
  oleans are current, and all 1684 local links resolve. No holes, custom axioms,
  warnings or errors were found in scope; `git diff --check` passes. Twenty-eight
  public theorem audits, eight controls and two readiness-definition checks were
  added. Log: `tmp/variable-overlap/source-raw-visible-full-build.log`.

  Remaining B9/B10 acceptance obligations:

  1. **Open — actual raw internal availability and source_reachable_internal_match.**
     For an enabled historical internal phase, construct an actual reduction or
     the required weak internal sequence from the related raw partner. Communication
     needs two compatible ready prefixes in that same raw state, including
     interleaved local scopes. A conditional additionally needs an actual ground
     guard before original thenBranch/elseBranch can apply. Current forward
     interpretation and conditional-location theorems do not supply this converse.
     The new visible readiness lemmas establish separate input/output existence,
     not a common communication redex or a valid conditional action.
  2. **Open — integrate all clauses into one source relation.** Retain actual
     execution provenance, the shared reached phase/name coordinates, full frame
     presentations and complete handle bijections. The input and bound-output
     successor clauses are now checked in source_reachable_input_match and
     source_reachable_bound_match. Add internal closure and symmetric matching;
     retain old-handle output exclusion, rejection and freshness. B9 is complete
     only when these acceptance conditions all hold together.
  3. **Open — source_reachable_weak_bisimulation and
     source_election_weak_bisimilar.** Assemble the source-level weak labelled
     bisimulation from the completed B9 relation, with actual Named.StaticEq
     observations and the original action semantics.
  4. **Open — scopedVoterElection_ballot_secrecy.** Transfer to the actual scoped
     elections with documented freshness, arbitrary valid ground parameters and
     arbitrary finite administration size. Audit public hypotheses, full E/E0
     observations and independent controls. Do not assume the remaining
     correspondence or report stage matching/static equivalence as secrecy.

  The retrospective reuse audit stays after B1–B10 secrecy completion.

  Concrete next obstruction: SourceExtendedSyntax.Reduction.thenBranch and
  elseBranch require a syntactically ground Formula embedded into the raw variable
  context. A semantic realization of a ready branch does not itself satisfy that
  constructor. The checked current frame presentation supplies actual provider
  constraints, but a derivation must use them to ground the ready guard while
  retaining its continuations and all providers. Compare that focused guard
  rewrite with whole-live-code normalization before adding a larger layer. The
  new visible proofs show that whole-live-code normalization was unnecessary for
  input and output; no such premise was added. Internal communication separately
  needs a simultaneous prefix-extraction argument. These are proof obligations,
  not new attacker restrictions, source rules or supplied invariants.

  See [the maintained dependency map](docs/research/helios-proof-blueprint.md)
  and [integrated source evidence](docs/research/helios-source-coordinated-phases.md).

  B9's general actual raw internal matching is now machine-checked, integrated
  and audited. source_reachable_internal_match includes acceptance and rejection;
  JointOpening.internal_available derives all prefix, local-presentation and
  guard-grounding witnesses from the actual current frame and full joint opening.
  Both actual successors retain reached phases, complete frames and observations.
  Together with the checked input/output clauses this closes individual action
  matching, but the combined successor-preserved source relation remains open.

  Integrated evidence: `lake build` succeeds; the clean targeted control build
  also succeeds. The current full log contains 4926 standard-only nonempty and
  103 axiom-free reports. The claims checker covers 4024 public theorem entries
  and 132 current-status documents. Ten changed Lean oleans are current; all 1684
  local links resolve. No holes, custom axioms, warnings or errors were found in
  scope; `git diff --check` passes. Twenty-seven public theorem audits include
  seven controls, with both guard truth values quantified. Log:
  `tmp/variable-overlap/source-raw-internal-full-build.log`.

  Remaining B9/B10 acceptance obligations:

  1. **Open — integrate all clauses into one source relation.** The individual
     source_reachable_internal_match, source_reachable_input_match and
     source_reachable_bound_match clauses are now checked. Package their current
     phase, actual execution provenance, full presentations and shared handle/name
     coordinates, and prove the same relation at every pair of actual successors.
     Cover structural changes, internal reductions, unchanged public input labels,
     fresh outputs, reindexing and both voting directions. Preserve old-handle
     output exclusion and rejection. Intended declarations: SourceElectionRelation
     with structural, internal, free, bound and reindex closure; its initial scoped
     membership must derive all fields from the documented freshness conditions.
  2. **Open — source_reachable_weak_bisimulation and
     source_election_weak_bisimilar.** Assemble the source-level weak labelled
     bisimulation from the completed B9 relation. The observations must be actual
     full Named.StaticEq presentations and actions must use the original Named
     semantics, with exact fresh output domains. Prove symmetry and preservation;
     do not assume correspondence at this interface.
  3. **Open — scopedVoterElection_ballot_secrecy.** Transfer to the actual scoped
     elections with documented name, nonce/parameter and channel freshness,
     arbitrary valid ground candidates and finite administration size. Audit the
     full E/E0 observations, rejection, public hypotheses and independent controls.
     Stage matching, equal tallies and static equivalence alone are insufficient.

  The retrospective reuse audit stays after B1–B10 secrecy completion.

  See [the maintained dependency map](docs/research/helios-proof-blueprint.md)
  and [integrated source evidence](docs/research/helios-source-coordinated-phases.md).

  B9 is complete: SourceElectionRelation.initial supplies actual scoped
  membership; symm/staticEq/structural/reindex/internal/free/bound preserve
  one relation through every original action with both actual executions,
  complete frames, handle coordinates and private-name policies. Reachable
  frame reconstruction and rejection/old-output exclusions remain checked.
  B10 is the current blueprint milestone; no final secrecy theorem is claimed.

  Integrated evidence: the targeted controls and required `lake build` pass.
  The full log contains 4951 standard-only nonempty and 103 axiom-free reports;
  the claim checker covers 4047 public theorem entries and 132 current-status
  documents. Five changed oleans are current, all 1646 local links resolve, and
  no holes, custom axioms, warnings or errors occur in scope. `git diff --check`
  passes. Twenty-three public theorem audits, seven controls and two definition
  audits were added. Log: `tmp/variable-overlap/source-election-relation-full-build.log`.

  Remaining B10 acceptance obligations:

  1. **Open — source_reachable_weak_bisimulation.** Package the completed
     SourceElectionRelation clauses as one symmetric source weak labelled
     bisimulation. Use actual Named.StaticEq, original Reduction/FreeStep/
     BoundOutput and finite internal closures. Keep full label domains and the
     typed fresh output coordinate explicit. Check this definition against the
     historical Definition 2; no conditional correspondence premise is needed.
  2. **Open — source_election_weak_bisimilar and
     scopedVoterElection_ballot_secrecy.** Instantiate that relation with the
     actual scoped initial elections using SourceElectionRelation.initial and
     documented name, nonce/parameter and channel freshness. Quantify arbitrary
     valid ground candidates, positive candidate count and finite administration
     size. Retain full E/E0 observations, rejection and independent positive and
     negative controls; run the public theorem, full build and writing audits.

  The retrospective reuse audit remains after B1–B10 secrecy completion.

  B10 acceptance is complete. See
  [the final theorem and definition audit](docs/research/helios-source-coordinated-phases.md)
  and [the completed blueprint](docs/research/helios-proof-blueprint.md).

  Integrated evidence: the clean targeted controls and required `lake build`
  pass. The final full log contains 4967 standard-only nonempty and 103 axiom-free
  reports; the claims checker covers 4058 public theorem entries and 132 current
  status documents. Seven changed oleans are current. No holes, custom axioms,
  warnings or errors occur in scope; `git diff --check` passes. Eleven public
  theorem audits, five controls and five weak-semantics definition audits were
  added. Log: `tmp/variable-overlap/source-ballot-secrecy-full-build.log`.

  B1–B10 acceptance is complete. No symbolic source-correspondence, action,
  frame, freshness or final-secrecy obligation remains open at the stated scope.
  The next authorized task is the retrospective reuse audit in task list.md:
  freeze the completed dependency snapshot, inspect candidate substitutions,
  validate representative isolated adapters and quantify demonstrated reuse versus
  estimates. It is follow-on work, not a premise of this theorem. Computational
  soundness, concurrent elections and other protocol extensions remain separate.

- [ ] Generate an explanatory trace/table from the model and prove that every
  displayed tally or probability equals the quantity in the supporting theorem.
  Show the original, whole-ballot and component-weeding cases. Audit prose
  against the actual claim; list unresolved variants explicitly.

## 4. Concrete Helios attack, repair and computational security

Milestone position: **3/3 proof milestones complete under the revised boundary; publication package complete**. Step 1
(concrete attack) and Step 2 (repair and honest correctness) are integrated and
audited. Supporting library selection and toolchain migration are also complete.
Report this position in progress updates; it does not estimate effort remaining.

Status: **proof complete under the revised boundary; publication package complete**. VCVio is selected after native library builds and
checked interface probes. The concrete public proof-reuse attack now checks
in the scoped three-voter probabilistic game, including rejection and trustee
observations. The selected concrete repair now rejects the attack and preserves
honest validation/tally correctness in that execution scope. The revised
conditional secrecy theorem now checks over the encoded attacker resource
interface, with source coverage derived by clocking. Its strict-PPT interpretation
uses the explicit external argument recorded below. The final case-study
assumption/scope audit and publication package are complete.
Evidence is recorded in [the results ledger](docs/research/helios-results.md#concrete-computational-library-validation-2026-09-12-in-progress). The computational secrecy milestone is complete under the explicit external-efficiency
and strict-PPT interpretation boundary. This phase uses
actual cryptographic algorithms and a probabilistic security game; it is
separate from the completed historical symbolic proof. The library checks
below support the concrete example. General election-language machinery and
symbolic-to-computational transfer follow this case study.

- [x] Separate the retained computational case study from deferred execution evidence:
  [38 explicit roots](ExplainableCrypto/Helios/Computational.lean) retain the attack,
  repair/correctness, secrecy and independent controls (174-module closure);
  `HeliosExecution` also builds the remaining 408 modules at unchanged paths/pins.
  Default/full builds, actual Lean import-set checks, endpoint/exact-name axiom
  audits and selected independent fixtures pass. Routine CI checks the case study;
  manual `deferred: true` preserves the full gates/reference build. PDF and proof
  sources are unchanged. [Evidence](docs/research/helios-results.md#computational-case-study-target-split-2026-09-15).

- [x] Rewrite the Helios PDFs for external readers: the [mathematical reference](docs/formal-reference/main.pdf)
  presents protocol/games before results, mathematical bias and conditional secrecy,
  all attacker/efficiency assumptions, the accuracy degree and external standard-DDH
  argument. The [historical catalogue](docs/formal-reference/catalogue.pdf) preserves
  component mathematics with obsolete status assertions removed. Independent build,
  citation/statement/axiom gates and rendered-page reviews pass for both; README,
  source navigation and CI are synchronized. Proofs and pins are unchanged.
  [Evidence](docs/research/helios-results.md#reader-facing-reference-and-historical-catalogue-2026-09-15).
  Reader polish (2026-09-16) removes forced section and post-abstract breaks, adds the group-notation
  dictionary, source/frame terminology, adjacent efficiency explanation, author
  and computational reading path. The rebuilt reference passes its full gates
  and rendered-page review. [Evidence](docs/research/helios-results.md#reference-reader-polish-2026-09-16).

### Supporting prerequisite: validate the computational library choice

- [x] Build the selected VCVio modules in an isolated Lake project using its
  pinned toolchain. Inspect the ElGamal and Σ-protocol declarations and their
  kernel-reported axioms; review security assumptions independently. Record
  exact commands, revisions and failures. The initial probe kept the demo
  toolchain fixed; the subsequently authorized migration below supersedes that constraint.
- [x] Build the corresponding CatCrypt-core ElGamal and Chaum–Pedersen modules
  separately. Check the visible/private transcript boundary and the adapter
  required between `CyclicGroup` and `GroupParam`. Do not infer build failures
  from missing local toolchains, or infer complete proofs from filenames.
- [x] Compare a minimal ballot-game prototype in the two frameworks: adaptive
  ballot observation/submission, stateful acceptance, one checked distinguisher,
  and one exact computed probability connected to the semantics. Choose one
  framework based on proved interfaces and adaptation work. Record the decision
  and add only the chosen framework as a pinned Lake dependency when needed.

  Prerequisite validation complete: both selected native builds, the CatCrypt
  group adapter and both adaptive board/probability probes pass with standard
  axioms. [Reproduction commands](docs/research/computational-probes/README.md).
  VCVio was initially validated in a separate package. The authorized migration
  now integrates it under `ExplainableCrypto.Helios.Computational` on Lean/Mathlib
  4.33.1; upstream reference pins remain unchanged. The earlier independent
  builds and 15-page reference audit closed the prerequisite only; the unified
  migration audit is recorded below.

- [x] Unify usable project code on Lean/Mathlib 4.33.1 with pinned VCVio; move
  concrete proofs to `ExplainableCrypto.Helios.Computational`, preserve symbolic
  statements and controls, and run the unified build and formal-reference audits.

  Unified migration complete and audited: root `lake build` passes on 4.33.1.
  All existing public theorem headers in changed tracked files are preserved;
  the final symbolic secrecy module is unchanged. Compatibility edits replace
  fragile simplification/rewriting with explicit equalities and enumerate the
  same finite voter/vote/policy types. The full claims audit, 73 symbolic and
  14 computational PDF citations, five typed restatements and gate tests pass.
  All 34 current computational theorem axiom reports are standard only. The
  updated 16-page PDF is visually reviewed. Reference pins/checkouts remain
  unchanged. This closes the migration, not the computational secrecy goal.

### Step 1: prove the attack in the concrete setting

- [x] Fix the exact historical variant for Smyth's neutral-ciphertext/proof-reuse
  attack. Specify the ElGamal algorithms, message and ciphertext domains,
  disjunctive ballot proofs, Fiat–Shamir challenge inputs, validation, board
  updates and all public observations. Resolve or explicitly delimit the
  `(1,1)` domain-check ambiguity recorded in section 1; do not silently add
  checks or stronger proof assumptions. Give a source mapping for the selected
  construction and an independently derived honest-ballot fixture.
- [x] Construct the malicious ballot in Lean, prove the actual validation
  checks accept it in the identified vulnerable variant, and exhibit the
  public distinguisher between swapped voting worlds. Connect the algebraic
  witness to a probabilistic ballot-privacy game and prove its success
  probability or distinguishing advantage under explicit conditions. Keep
  attacker inputs separate from honest generation and prove an honest ballot
  is accepted. Do not count the existing finite symbolic attack certificates
  as completion of this concrete milestone.

  Checked scope: Smyth's at-most-one/abstention construction, two candidates,
  two honest voters and one dishonest voter, one honest trustee and a fixed
  cast-only schedule. `BallotProof` and `ProofReuse` implement the arithmetic
  attack. `Board` checks actual submissions and preserves accepted entries on
  rejection. `Trustee` constructs and validates the published key/decryption
  proofs. `HonestSampling` samples both honest ballots without removing
  collisions. `BallotSecrecyGame.lean` exposes public messages to
  a stateful attacker; `ballotSecrecyGame_proofReuse_success` proves success
  at least `1 - 6/(|F|-1)` (truncated at zero). The bound assumes a finite field
  and injective generator exponentiation, not freshness or a missing proof
  correspondence. It covers all rejection/collision executions.

  Independent modulo-23 controls check honest and malicious validation, literal
  trustee transcripts, invalid-proof rejection, retained-board tallying after
  honest rejection and fresh abstention without copying. The independent nonce
  oracle enumerates all 10,000 nonzero tuples in each world with no failure of
  the sufficient good event. Root `lake build` and the integrated
  reference/axiom audit pass: 73 symbolic and 23 computational printed citations,
  37 local links, five typed restatements and five gate tests. All 73 current
  computational theorem axiom reports are standard only. The warning-free
  17-page PDF has been visually reviewed. These results are local, uncommitted
  and unpushed; see the results ledger for commands and scope.
  The [concrete model](docs/research/helios-computational-model.md) explicitly
  delimits raw/non-subgroup encodings, optional audit paths, authentication and
  the absent security-parameter/PPT implementation bridge. This completes the
  concrete attack witness in that scope, not security of the repaired protocol.

### Step 2: add the repair and check its behavior

- [x] Specify the precise concrete repair, with its source provenance or an
  explicit label as a newly proposed variant. Implement it in the same model,
  preserving the stated observation and corruption boundaries. Prove the known
  attack fails and independently generated honest ballots still validate and
  tally correctly. Record any changed cryptographic assumptions. These are
  regression and correctness results; mark general computational secrecy as
  outstanding until step 3 is complete.

  Checked repair: BPW sections 4–5, strong statement hashes for ballot/key/trustee
  proofs plus explicit-and-implicit ciphertext weeding. The scoped public game
  retains nonzero sampling and rejection without deleting accepted entries.
  `executeRepairedAttack_rejected` and `repairedAttackWorld_rejection_probability`
  prove deterministic and probability-one rejection. `strongHonestBallot_valid`
  proves honest proof validity; `repairedHonestPair_decrypts` proves the actual
  accepted honest pair's group tally. `repairedHonestPair_rejection_le` accounts
  for all independently sampled collisions with bound `9/(|F|-1)`.
  `RepairControls` and the independent modular oracle retain accepted honest
  worlds, literal trustee transcripts, decoded tallies, nonconstant tallying,
  weak-proof rerandomization and the failure of strong hashing alone to block
  aggregate reuse. The root build and integrated PDF/axiom audit pass: 73 symbolic and 33
  computational printed citations, 39 local links, five typed restatements and
  five gate tests. All 111 current computational theorem reports use standard
  axioms only. The warning-free 18-page PDF has been visually reviewed. The [model](docs/research/helios-computational-model.md) records the
  differences from BPW's sampling and simulated-tally privacy game. This closes
  the concrete repair regression/correctness milestone in the documented scope;
  it does not complete a security reduction or enlarge the attacker coverage.

### Step 3: prove computational ballot secrecy of the repaired protocol

**Agreed finishing criterion (2026-09-15).** The concrete computational case
study is complete when a checked theorem covers the intended PPT attackers in
the accepted fixed three-voter, two-candidate, one-honest-trustee game, preserves
the original public game distribution and proves negligible ballot-secrecy
advantage under explicit cryptographic, parameter and implementation assumptions
and the two named, externally justified reduction-efficiency hypotheses.
No source or attacker-coverage correspondence may remain assumed. Required
independent controls and final theorem/build/axiom audits must pass, followed by
the synchronized publication artifacts. Only mechanizing reduction efficiency
has been relaxed; neither the protocol nor the intended attacker class changes.

**Proof obligation discharged (bounded attempt, 2026-09-15):** law-preserving
attacker coverage, including actual serialized input bounds, private-state growth
and clocking, now checks for the specified resource interface. C12 records the
exact composed theorem and external strict-PPT interpretation. The final scope/assumption audit and publication synchronization are now complete.
Machine-efficiency construction in C5–C8 is deferred and is not a prerequisite
for this revised deliverable; its checked evidence is preserved. C5's source
attacker-coverage obligation is discharged through C12 for `Family`. Historical positive-attack
oracle transport remains a separate C9 validation item, outside this secrecy
closure task. Broader election models and the symbolic-to-computational transfer
question are subsequent research decisions.

Completion of this concrete milestone does not establish symbolic-to-computational
transfer. General election-language and transfer-framework work remains deferred
until this concrete goal is complete.

#### Computational checkpoints: current tracking view

**Historical checkpoint accounting: 6/12 complete (C1–C4, C10–C11).**
C5–C8 machine-efficiency work is deferred, not completed. C12 now closes the revised proof through checked attacker coverage; C9's historical attack transport remains
separate. The original twelve checkpoints no longer describe twelve required
steps toward the revised finish line.
The earlier 2026-09-15 closing audit exposed the missing `PreparedFamily`
coverage correspondence. The subsequent bounded attempt now derives it and
composes secrecy for the original attacker. This closes that source-level gap
for the stated resource interface; the strict-PPT interpretation and its external
boundary are explicit in C12 and the latest results record. Only mechanized
efficiency is deferred; no source correspondence is assumed. See the earlier
[closing audit and external argument](docs/research/helios-computational-closing-audit.md).
The top-level count is **3/3 proof milestones complete under the revised boundary; publication package complete**. These
checkpoints separate completed prerequisites from remaining security obligations;
neither count estimates effort, time or a percentage of the final proof.
The [computational dependency map](docs/research/helios-proof-blueprint.md#computational-proof-dependencies)
uses these identifiers. This section is the only task list; the detailed records
below retain provenance and do not introduce additional milestone counts.

- [x] **C1 — Actual ballot-proof construction and simulation prerequisites.**
  Acceptance: completeness, special soundness and simulation for the actual
  disjunctive construction, with full-statement Fiat–Shamir binding and the
  historical nonzero-sampling loss explicit. Evidence: `ballotSigma_complete`,
  `ballotSigma_speciallySound`, `ballotSigma_hvzk`, and checked oracle/programming
  correspondence and independent controls below. This is not adaptive soundness
  or ballot secrecy for the full election. Dependencies: completed Steps 1–2.

- [x] **C2 — Joint extraction for the existing post-prefix submission scope.**
  Acceptance: all three witnesses refer to one actual accepted source ballot,
  with nonce/aggregate and integer at-most-one consistency, exact replay/source
  correspondence and explicit loss/query bounds. Evidence:
  `repairedSubmissionPrimeBits_extract_eq`, `_valid`, `_consistent`, `_le`, and
  `repairedSubmissionPrimeBits_extract_total_bound`. This closes that documented
  scope; earlier/interleaved attacker queries and the full election belong to
  C9–C10. Dependencies: C1.

- [x] **C3 — Finite source data and fair-bit distribution bridge.**
  Acceptance: original finite replay/cache/log/public-data encodings and bounds;
  actual coin-query sampler, adaptive replacement loss and source-validity
  transport for the existing extractor. Evidence: original codec/size modules,
  `sampleFairBitRange_tv_le`, `runFairBitUniform_tv_le` and
  `repairedSubmissionFairBits_extract_{tv_le,valid,consistent,le}`. These are
  data/semantics and query-count results; host arithmetic costs are excluded.
  Dependencies: C2 for the extractor instance.

- [x] **C4 — Executed cache/log operations and source-handler correspondence.**
  Acceptance: actual lookup, guarded insertion, answer parsing and log append,
  with retained data, derived source-state bounds and correct rejection;
  exact source request tree/output/encoded successor states through every
  continuation. Evidence: `CacheReadMachine.source_cache_run`,
  `CacheInsertMachine.source_cache_run`, `LogAppendMachine.source_log_run`,
  `CacheHashHandler.hash_eq` and `.run_eq`. Host loading, numeric conversion,
  transfers and continuations remain outside this checkpoint. Dependencies: C3.

- [ ] **C5 — Fix the effective attacker and oracle-machine execution contract.**
  **Current disposition: machine-execution construction deferred.** Preserve
  the results and historical obligations below. Semantic intended-attacker
  source coverage is now derived under C12 for the specified `Family` interface;
  the strict-PPT implementation interpretation remains explicitly external.
  **General query-export experiment (2026-09-15): proved, integrated and
  audited.** The authorized window is 04:28:44–05:58:44 UTC; stop by
  that deadline. `NativeQueryExportFrame.charged`, `.native_result`,
  `.native_storage` and `.private_retained` prove actual finite execution
  exporting exactly `OracleTapeDispatch.readWord` for arbitrary head/before/after
  cell lists, preserving both complete encoded halves, the original head and
  arbitrary independent private words, with scratch restored. Executed entry
  prepares the head; executed exit removes it and restores the register.
  Source clock is `2*after.length+6`; instruction-derived charge is at most
  `12*after.length+36`. No supplied correspondence, frame or cost certificate.
  Each independent core/actual-head gate checks 1,522 originals; five/seven
  instruction mutations respectively and thirteen kernel controls retain empty,
  false, internal-blank, postblank-data and storage-corruption cases. Root build, complete
  audits, both gates and reviewed reference §14.133/Theorem 14.163 pass; exact
  evidence is recorded in the results ledger.
  Reproduce: `lake env lean scripts/NativeQueryExportGate.lean`.
  Input is resident canonical cell encoding, including arbitrary internal and
  trailing blanks. The round-trip result below supplies one-call reply import/dispatch/composition;
  general native program compilation, external packing and intended standard-PPT
  coverage remain open. No C5 closure, additional
  fixed demonstration or framework migration; prior counterexamples remain.
  **Bounded oracle round trip (2026-09-15, 09:23:15–10:53:15 UTC):**
  general theorem proved, integrated and audited. Root build, full audits,
  independent gates and reviewed reference §14.134/Theorem 14.164 pass.
  `NativeRoundTrip.framed_correspondence`, `.native_correspondence` and
  `.framed_cost` prove the full actual event tree, represented native successor
  and instruction-derived bound for arbitrary finite cell lists/private words.
  The controller returns to the live label selected before memory reuse.
  Hash replies satisfy the explicit `limit`; both coins remain allowed.
  This is one oracle call, with canonical resident encoding and initially blank
  scratch; later continuation execution and physical lowering are not claimed.
  Reproduce: `lake env lean scripts/NativeRoundTripGate.lean`.
  Independent importer/whole-call gates and kernel controls cover empty/false
  replies, internal blanks, old answer data, corrupted storage and wrong returns.
  Exact original acceptance and reproduction evidence remain in the results
  ledger's general round-trip record. No C5/compiler/PPT closure is claimed.
  **Compositional efficiency feasibility (2026-09-15): checked obstruction.**
  The 90-minute window began 11:23:56 UTC. `CompositionalEncrypt.ppt` checks
  primitive composition for the actual fixed-carrier encryption formula;
  `CompositionalRejectProbe` uniformly packs the exact varying-family rejection
  reduction and exposes its first empty-cache preparation handler. Rejection
  PPT remains unproved. Pinned semantic handler substitution does not construct
  the combined executable realization, state-growth and runtime proof. Actual
  cache hit/miss/sharing controls and a checked n-call/exponential-size
  counterexample make that missing obligation explicit. These are targeted local
  checks, not completed computational secrecy or a publication batch. Full
  evidence/assumptions are in the results ledger's compositional feasibility entry.
  **Upstream substitution experiment (2026-09-15): checked partial results;
  no-go for immediate adoption.** Stopped within the 11:55:23–13:25:23 UTC cap.
  Scratch `tmp/handler-substitution-2026-09-15` freezes VCVio at `25f26bfee60d`.
  `Scratch.Substitution.CandidateStatement` is the exact typed, UNPROVED general
  proposition with explicit backend, representation and response assumptions.
  Uniform microsteps and caller-bound substitution check. `actual_lower_empty`
  identifies the original replay handler from empty persistent storage for every
  adaptive callback; `open_empty_bounds` proves entry/abstract-width growth.
  General closed PPT, a uniform cache-handler certificate and implemented storage
  costs remain unproved. A checked control rejects truncating excluded typed
  replies using only an allowed-response bound. This does not refute composition
  or establish that a new compiler is necessary. The exact residual route through
  other handlers, fair bits, varying-family encodings and standard-PPT adequacy
  is recorded once in the results ledger's upstream substitution outcome.
  Scratch build/axiom audit and root preservation checks pass; no checkpoint or
  full root-port closure. End this experiment here; no further component probes.
  Root proofs/pins and the full secrecy target are preserved. PDF/publication
  synchronization is deferred as required by this goal.
  **Bounded native compilation experiment (2026-09-15): proved, integrated
  and audited.** The authorized
  window is 03:24:38–04:54:38 UTC; stop no later than its deadline. Outcome:
  proved for the fixed adaptive program. `NativeWordCompiler.code` mechanically
  translates `NativeAdaptiveProbe.code`; `NativeAdaptiveRun.exact_run` proves the
  generated 19-step tree and full final stack/memory/halt state, with exact charge
  from actual instructions. `.native_correspondence` identifies the complete
  native eight-step query tree and terminal tapes. Both hash replies are arbitrary.
  `NativeAdaptiveCost.within` derives the bound
  `68 + 2*input.length + oldAnswer.length + 3*limit`; `.physical_run` reuses the
  existing primitive compiler at its derived clock under the bounded adapter.
  No correspondence, frame or cost certificate is supplied by callers.
  Independent gate: 810 exhaustive and three directed positives, four actual
  source mutations through the unchanged compiler, complete states/events/charges,
  no discards. Native blank-write/blank-move controls delimit unsupported programs.
  The initial boundary is six resident dense bit stacks, including independent
  private before/right words. Initial packing/loading, arbitrary internal blanks,
  a general compiler and intended standard-PPT coverage remain unproved.
  The fixed program itself establishes all states needed for successful moves
  and answer replacement. C5 remains partial; all checkpoint statuses are unchanged.
  Do not extend this experiment to full C5, further protocol construction or a
  framework migration. Reproduction: root `lake build`, then
  `lake env lean scripts/NativeAdaptiveCompilerGate.lean` and required audits.
  Status: partial; complete target-control finiteness and source-derived
  primitive-clock/handler transport and physical raw-input loading are checked.
  Intended standard-PPT attacker coverage and the actual scalar-handler contract
  remain active. Acceptance: define the efficient attacker/program representation,
  oracle suspension/resumption, loaded operand conventions, raw-input policy
  and cost accounting; demonstrate a concrete adaptive hit/miss interaction
  under that interface with a derived source correspondence and cost.
  It must admit the intended PPT attackers and preserve their public interface;
  unrestricted host callbacks and caller-supplied adequacy/cost certificates
  cannot stand in for this proof. Compare the narrow chosen route with the
  pinned library's actual limitations, preserving pins. Record any obstruction
  here before building additional infrastructure. Dependencies: C3–C4; C6
  supplies the scalar implementation used by the final interaction test.
  Source inspection confirms that VCVio's semantic `OracleMachine.toMachine`
  admits arbitrary host callbacks and gives no standard-PPT coverage or costs.
  The chosen contract requires fixed finite code independent of the security
  parameter, charged tape access/transfers, explicit oracle suspension and
  encoded inputs/responses. `BitOracleMachine` now reuses TM2 statements with
  fixed finite stack/label/local-memory types and explicit raw hash/coin ports.
  `local_run` derives exact existing TM2 execution; `resume_frame` retains other
  stacks. `BitOracleCanary.run_source` checks H(x), H(H(x)), H(x) with the full
  halted configuration and exact ghost length charge
  4+2|x|+2|a|+|b|+|c|. Five controls and 1524 independent raw-port cases pass.
  Integrated/audited: root build, exact-name standard-axiom audit and reviewed
  reference §14.76/Theorem 14.78 (pages 101–102) pass.
  `BitOraclePortTransfer.hash_transfer` / `.coin_transfer` now realize the
  actual request/response word movements in TM2, preserving full caller state
  and restoring empty private workspace. The request phase precedes all answer
  choices. Derived cost is at most nine times the raw charge, counting TM2 ticks
  plus one native event. `hash_handoff` / `coin_handoff` identify the actual
  raw OracleComp queries and full response-phase starts under every handler.
  Existing copy, stack-frame and return proofs are reused;
  a finite-memory frame preserves caller variables. Appending and stale-private-
  port shortcuts have checked counterexamples. Six dedicated controls and bounded
  independent interpreter fixtures pass. Integrated/audited: root build, exact-
  name standard-axiom audit and reviewed §14.77/Theorem 14.79 (pages 102–103;
  theorem page 103) pass. Reuse these phases for the open-machine assembly;
  do not rebuild their word movement.
  `BitOracleLoop.run_source` now derives costed query-tree execution for every
  finite raw source run in the assembled finite-control loop. `run_source_path`
  derives an actual micro-run with the same complete query/answer log and caller
  state, at most eleven times the branch charge. First-completion phase proofs
  avoid premature queries and derive empty private workspace before return.
  Integrated/audited: six Lean controls, 2,880 independent three-call fixtures,
  root build, exact-name standard-axiom audit and reviewed reference §14.78/
  Theorem 14.80 (pages 103–104; theorem page 104) pass. See the results ledger.
  This closes finite raw-program assembly/correspondence. The common-clock
  transport now checks in `BitOracleLoopBounded.run_source`/`.run_source_handler`:
  when every allowed-answer source branch halts with charge ≤B, 11B loop ticks
  preserve the complete query tree and all lawful handler effects. The explicit
  answer contract bounds hash output length, retaining every raw request.
  `BitOracleBoundedCanary.within` derives B=4+2|word|+4L and its complete halt;
  `.run_handler` has no caller-supplied cost/correspondence premise. Seven Lean
  controls, 2,880 two-clock fixtures, root build, exact-name standard-axiom audit
  and reviewed §14.79/Theorem 14.81 (page 105) pass. This increment is
  integrated/audited; reproduction is in the results ledger. The missing-halt padding claim has a checked
  counterexample. Next: standard oracle-tape embedding/quantitative bounds,
  actual scalar-handler response-width derivation and malformed-request policy.
  The actual complete algorithms' termination/cost bounds remain in C8.
  `TM2TapeCost.source_step` now derives a bound for Mathlib's existing full
  statement translation: 1+a(2(H+a)+2) TM1 ticks, preserving `TrCfg`, with a
  maximum stack accesses and initial stack-height bound H. Earlier pushes are
  included. `BitOracleTapeCost.request_step`/`.response_step` instantiate the
  actual framed port programs at a≤3, hence 6H+25 ticks per transition. Five
  Lean controls, 6,000 independent tape cases, root build, exact-name standard-
  axiom audit and reviewed §14.80/Theorem 14.82 (page 106) pass. This increment
  is integrated/audited; reproduction is in the results ledger.
  `TM2TapeRuns.run_packed` now constructs the initial presentation and derives
  code/height maxima and successor growth. For n deterministic source ticks,
  it proves exact canonical final tape equality within n(1+A(2(H+nA)+2)) TM1
  ticks, final stack height ≤H+nA. `BitOracleTapeCost.request_run` and
  `.response_run` apply this to complete actual transfers within B(6H+18B+7)
  ticks, deriving the retained caller frame and empty response workspace.
  Five Lean controls and 4,500 independent persistent-tape cases pass, including
  frozen-height and unreversed-packing counterexamples. Root build,
  exact-name standard-axiom audit and reviewed §14.81/Theorem 14.83 (page 107)
  pass. This increment is integrated/audited. Initial packing is a data
  representation, not physical loading. Native oracle-tape I/O, finite reachable
  syntax, primitive costs and full open-loop composition remain. These results
  do not close machine adequacy or C5. See the results ledger.
  `OracleTapeOutput.run_replacing` now executes outgoing native-tape export:
  clear a prior canonical query u, emit the actual selected word w in ordinary
  order and restore the entire packed work tape in |u|+2|w|+3 head-local
  two-tape transitions. `BitOracleTapeOutput.request_run` connects this to the
  actual request-preparation result with both region bounds derived. Seven Lean
  controls and 5,400 independent cases (fresh/reused query tapes) pass; root build,
  exact-name standard-axiom audit and reviewed §14.82/Theorem 14.84 (page 108)
  pass. This increment is integrated/audited. The prior native tape's canonical head
  position remains explicit. Response loading is discharged below. Native
  dispatch, physical input loading and full-loop finite-control/primitive costs,
  then the actual scalar-handler contract remain. C5 is partial.
  `OracleTapeInput.run_packed` now loads the native answer by actual head-local
  steps, erasing any old private word and preserving every other column. The
  exact bound is 3|oldPort|+4|answer|+6; both heads and the native answer are
  restored. Mathlib's existing push/pop updates are reused. `BitOracleTapeInput`
  `.load_request` derives the actual response-start tape; `.response_run`
  connects the full response execution and derives the resumed caller/empty
  workspace. Six controls and 5,400 independent cases pass; root build,
  exact-name standard-axiom audit and reviewed §14.83/Theorem 14.85 (page 109)
  pass. This increment is integrated/audited. Native dispatch and per-call composition are
  discharged below. Physical initial-input loading, finite-control/primitive-cost transfer and
  actual scalar-handler policy remain C5/C8. No all-PPT claim is inferred.

  `BitOracleTapeCall.hash_prepared_issue` now derives the native hash event
  from actual TM1 request preparation and physical export. `.answer_run` and
  `.received_run` execute physical loading and the consuming TM1 response in
  one loop, returning the exact resumed caller, native tapes and empty private
  workspace for every answer. `.coin_issue` retains the actual bit query.
  `OracleTapeDispatch.read_wordTape` identifies every original raw word; the
  native decoder stops at the first blank. Seven Lean controls and 2,880
  independent three-call/cache fixtures plus 2,000 prefix cases pass. The
  fixtures validate region composition and source cache/log expectations, not
  full TM1 loop timing. Root build, exact-name standard-axiom audit and reviewed reference
  §14.84/Theorem 14.86 (page 110) pass. This increment is integrated/audited. The next increment below composes arbitrary finite source loops; a common
  observation clock remains open. Physical
  initial-input loading, finite-control/primitive-cost transfer and the scalar
  handler contract remain C5/C8; answer-dependent region clocks alone do not
  close C5 or establish standard-PPT adequacy.

  `BitOracleTapeLoop.run_source` now constructs query-tree correspondence for
  every finite original source run, including arbitrary ordinary statements,
  hash/coin calls, early halt and aliased ports. `.realizes_path` gives an actual
  finite tape run with the identical complete query/answer log and final caller.
  Ready states retain canonical work/query presentation and empty private
  columns; no caller supplies those certificates. The machine stores explicit
  tapes and finite return metadata, never a whole source caller. Existing call
  transitions and transfer proofs are reused. `BitOracleTapeCompute.run` handles
  one ordinary statement by saving its result label and halting; `.compute_run`,
  `.hash_issue`, `.coin_issue`, `.reply_run` derive bounds for the actual loop
  regions. Eight Lean controls cover mixed adaptive execution, occupied caches,
  aliasing, coins and goto/halt failures. A separate source/finite-return
  interpreter campaign passes 3,600 cases; it does not measure TM1 timing.
  Root build, exact-name standard-axiom audit and reviewed reference
  §14.85/Theorem 14.87 (page 111) pass. This increment is integrated/audited. This closes
  arbitrary finite source-loop correspondence, not a common runtime bound.
  Common-clock transport is discharged below with source termination retained
  in its contract. Derive the actual algorithms' bounds in C8. Physical initial-
  input loading, finite reachable syntax/primitive costs and scalar-handler
  policy remain open. C5/counts are unchanged.

  `BitOracleTapeLoop.run_source_bounded` and `.run_source_handler` now derive
  the common tape-loop clock 650B(H+B+V+1)^2, with H the actual initial source
  height, B the original source charge bound and V the previous-query length.
  The existing `Within` termination/charge and `Allowed` answer contract are
  reused unchanged. `run_costed` derives all execution witnesses and successor
  growth, preserving current height + remaining source budget ≤H+B+V. The
  complete caller/query tree and lawful handler effects agree at that clock.
  `observeCaller` is proof-side full-state interpretation, not a free runtime
  decoder or new protocol disclosure. `BitOracleTapeBoundedCanary.run_handler`
  derives its own termination and B=4+2|word|+4L; no caller supplies a compiler
  or source-cost certificate for this instance. Six controls include cache
  hits, zero-width answers, height growth and actual live-padding failure.
  Independent fixtures cover 12,000 regional inequalities and 3,600 sampled
  word-transition paths; they do not measure TM1 timing or prove `Within`.
  Root build, exact-name standard-axiom audit and reviewed reference
§14.86/Theorem 14.88 (page 112) pass. This increment is integrated/audited. Next: finite
  reachable syntax and primitive-step cost transfer for this fixed tape loop.
  Physical initial-input loading and the actual scalar-handler width/raw-message
  policy remain C5/C8, with C6 supplying scalar execution. The clock counts
  tape-loop transitions containing TM1 ticks; full standard-PPT adequacy and
  actual protocol/reduction runtime bounds remain open. C5/counts are unchanged.
  This is a raw-word interface test, not the scalar-backed election-handler
  canary. Standard open-oracle embedding and its quantitative transfer bounds,
  scalar/codec connection and raw-message policy remain open. The charge is
  proposed interface instrumentation, not an asserted TM0 cost. Mathlib's
  existing TM2-to-TM1 theorem covers deterministic segments; it supplies neither
  the standard oracle-tape port translation nor quantitative adequacy. Preserve
  pins and
  resolve that adapter boundary before further local routines.

  The actual computation, request and response regions now execute through
  Mathlib's unchanged TM1-to-TM0 compiler with derived primitive move/write
  bounds. `TM1PrimitiveCost.run` gives n*K for supported n-tick TM1 runs;
  `BitOraclePrimitiveCost` derives finite support and K from fixed source code
  and applies it to all three complete regions. Six literal controls and 4,800
  independent tree/flat-code cases pass. Root build, exact-name standard-axiom audit and reviewed reference
  §14.87/Theorem 14.89 (page 113) pass; this increment is integrated/audited. The next C5 obligation is composing these
  primitive regions with the existing physical native-tape transfers and events
  in the full oracle loop, deriving its global finite support and clock. Initial
  loading, scalar policy, standard-PPT attacker coverage and actual protocol/
  reduction costs remain open. Counts remain 2/3 main milestones and 6/12 checkpoints.

  The primitive oracle loop now composes the existing native I/O with the
  pinned compiler's deterministic execution. `step_supported`/`run_supported`
  derive successor closure for all raw replies; `stepAllowance_le` derives a
  fixed code factor G. `run_tape` preserves the complete finite query tree and
  all lowered states within n*G primitive-loop transitions. `run_ready` derives
  initial support automatically. Eight controls include actual adaptive runs,
  aliasing, coins, zero-clock/live-return negatives and the general refinement.
  Root build, exact-name standard-axiom audit and reviewed reference
  §14.88/Theorem 14.90 (page 114) pass; this increment is integrated/audited. Next: prove the complete
  target-state finite-control invariant and primitive common-clock/handler
  transport using the existing source termination contract. Initial loading,
  scalar policy, standard-PPT attacker coverage and actual algorithm costs remain
  open; C5 stays partial and counts remain 2/3 main milestones and 6/12 checkpoints.

  Target finiteness and the primitive source clock now check. The target
  invariant covers every intermediate compiled instruction and native successor;
  `reconstruct` proves that finite control plus the three tapes recovers the full
  state. `run_source_bounded`/`run_source_handler` derive clock
  650*G*B*(H+B+V+1)^2 from the original source halt/charge and answer contract,
  including intermediate tape-run halt. The adaptive canary derives its own
  source bound. Eight new controls, root build, exact-name standard-axiom audit and reviewed
  §14.89/Theorem 14.91 (page 115) pass; this increment is integrated/audited.
  Next C5 obligations: physically load the initial input, prove intended
  standard-PPT attacker coverage and derive the actual scalar handler's raw-input/
  response-width policy (using C6). Actual full-algorithm bounds remain C8.
  Counts remain 2/3 main milestones and 6/12 checkpoints; C5 and secrecy are open.

  `BitOracleInitialInput.load` now derives the physical startup from blank work
  storage and a native raw input word. A bottom-marker write, the existing input
  loader and finite handoff reach the exact canonical ready state within
  4|word|+8 steps, with all other/private columns empty and input/head restored.
  `.run_source_bounded` / `.run_source_handler` compose that startup with the
  existing source clock and complete query-tree/handler effects. The derived
  startup time is shared by every oracle branch; no live padding is assumed.
  Arbitrary malformed bits are loaded unchanged; actual parsing/rejection and
  operand distribution remain source work. Six Lean controls and independent
  physical-loader fixtures pass. Root build, exact-name standard-axiom audit and
  reviewed §14.90/Theorem 14.92 (page 116) pass; this increment is
  integrated/audited.
  Next: intended standard-PPT attacker coverage and actual scalar-oracle policy;
  C5 remains partial, with counts unchanged at 2/3 and 6/12.

  `BitTapeCoverage.source_run` / `.native_step` now cover ordinary local
  computation of arbitrary fixed finite-label TM0 machines over blank/false/
  true cells. Two bit stacks plus a finite current-cell register represent each
  tape; moves/writes agree with pinned TM0 semantics. `.charged_run` derives
  charge ≤7f for every finite run. `.within` / `.primitive_run` connect actual
  native halt to the existing source contract and primitive compiler clock.
  Every native tape has a finite representative, but representation is
  proof-side: physical raw input conversion remains required. Six controls and
  48,000 independent tape transitions pass. Root build, exact-name standard-
  axiom audit and reviewed §14.91/Theorem 14.93 (page 117) pass; this local
  component is integrated/audited.
  This closes the local-computation component of coverage only. Next coverage
  obligations: raw input-to-cell conversion and native coin/hash suspension,
  query/answer transfer and successor framing under the same representation.
  Then close intended standard-PPT coverage; actual scalar policy remains
  separate. C5/counts are unchanged. Do not infer coverage from this local result.

  `BitTapeInput.run` now executes raw input-to-cell conversion in exactly
  2|word|+3 source transitions. `BitTapeStart.run` links conversion to arbitrary
  native code with a separate halt label and derived source duration/charge.
  `.physical_run` starts from blank work/native raw input and returns the complete
  native result at u+650*G*B*(|word|+B+1)^2, with u≤4|word|+8 and
  B=7(2|word|+f+4). Only the original native halt bound f is assumed; source
  presentation, conversion and cost premises are derived. The source-cost
  induction is reused in `BitOracleMachine.compute_run_cost`; the older native
  coverage charge theorem now delegates to it. Seven controls, including actual
  physical execution, and 3,000 independent conversion fixtures pass. Root build,
  exact-name standard-axiom audit and reviewed §14.92/Theorem 14.94 (page 118)
  pass; this connection is integrated/audited. This closes input conversion
  for local tape computation.
  Next: native coin/hash suspension, query/answer conversion and successor framing
  under the same representation, then full intended PPT coverage. Actual scalar
  policy remains separate. C5/counts stay partial, 2/3 main and 6/12 supporting.

  `NativeOracleTape` now fixes the remaining native reference interface:
  three ordinary blank/false/true tapes, finite current-cell transition input
  and finite commands, independent head-local actions, and the unchanged raw
  native dispatch. `.hash_step` / `.coin_step` / `.oracle_successor` derive exact
  events, selected return labels, preserved work/query tapes and replacement
  answers for all supported replies. Six controls include a checked private-
  frame counterexample to aliasing work and answer tapes. 3,000 independent
  native-event fixtures, root build, exact-name standard-axiom audit and reviewed
  reference §14.93/Theorem 14.95 (pages 118–119) pass; this increment is
  integrated/audited. This is reference
  interface agreement, not source compilation or full attacker coverage.
  The single-tape representation is insufficient for independent query/answer
  heads. Extend it to six cell stacks/three finite head registers. Intended
  `NativeOracleCompile` declarations (planned, not checked): `.local_step`,
  `.query_run`, `.answer_run`, `.run`, `.within`. They must derive local-action
  matching, exact request prefix extraction, framed answer conversion, successor/
  query-tree correspondence and native-time/answer-width polynomial bounds.
  Prove any normalization needed for intended standard-PPT coverage; a word-
  buffer interface alone cannot substitute for it. Scalar policy and C6–C8
  algorithm/runtime obligations remain separate. Counts remain 2/3 and 6/12.

- [ ] **C6 — Execute scalar sampling, reduction and digit handoff.**
  **Current disposition: deferred machine-efficiency work; not a prerequisite
  for the revised secrecy deliverable.** The directions and partial results
  below are historical evidence, not the current instruction to resume execution
  chains. Preserve the checked arithmetic and controls.
  **Convergence correction (user steering, 2026-09-15):** stop extending the
  protocol with a separate source-specialized execution chain and raw wrapper
  for each repeated proof request. Current arithmetic/serializer results remain
  valid, but this decomposition repeats layout, source, runtime and audit work
  without closing the complete adaptive-caller obligation. Before another such
  chain, validate a narrowly scoped complete proof-request executor with a fixed
  entry/return contract over actual statement/scalar/current-state inputs and a
  derived cost bound. Reuse existing numeric, insertion and history machinery.
  The acceptance test is two successive distinct actual source requests using
  the same executor theorem, with successor state/width/frame conditions derived
  and preserved; retain zero modular nonce sums and collision/sticky controls.
  A theorem that assumes the source correspondence or a cost certificate fails
  this test. Assess the standard-PPT attacker/continuation interface alongside
  this test: another honest-constructor prefix does not discharge C5 coverage.
  Record the finite route from that executor through full election execution,
  the exact DDH reduction runtimes and the all-PPT family endpoint. Keep all
  original C6/C5/C7/C8/C9/C12 acceptance conditions; do not rename partial work
  as a completed checkpoint. This is a concrete reuse/composition test within
  Helios, not a new election language or general compiler project.
  **Bounded goal (2026-09-15): architecture assessment, now integrated/audited.**
  Original acceptance: finish the
  already-started distinct p1/total execution test with actual reentry, preserved
  state and derived combined cost, or report a concrete obstruction without
  requiring its solution. Assess removed proof repetition and the demonstrated
  routes versus uncertainties in C5/C6/C7/C8/C9/C12. Recommend continuing, a narrow
  representation change or suspending, with evidence. Synchronize this task list,
  blueprint, ledger, README and reference PDF; build, audit, commit and push, then
  stop before further protocol construction. The intended secrecy theorem and
  every original checkpoint acceptance condition remain unchanged.
  Current reuse-test evidence: `PrimeProofRequest.charged`, `.execution_source`
  and `.run_support` prove a complete resident request for arbitrary typed nonce
  and current state, with derived charge. `PrimeProofRequestReentry.charged`
  proves actual cleanup and nonce preparation; `PrimeRemainingProofRequests`
  derives both historical source presentations, retained frames and zero-safe
  total statement. `PrimeRemainingProofCaller` links one raw prefix and the same
  executor twice. Its independent full-state native test and two fault controls
  pass. `PrimeRemainingProofCaller.linked_run`, `.execution_source`, `.run_support`
  and `.physical_run` now check from the original raw input, using derived bounds
  and the same bounded physical adapter. `PrimeRemainingProofSource.source_run`
  and `.endpoint_outputs` tie the final proofs/state to the original two queries.
  The test and checkpoint-route assessment are complete. Root build, full axiom
  and reference audits, repeated controls and reviewed PDF pass. Recommendation:
  provisionally retain the resident route; full architecture feasibility remains
  unestablished because C5 coverage and C8 exact reduction runtime are unresolved.
  Stop further protocol construction after publishing this checked increment.
  The reentry writer-port defect has a retained checked counterexample. Both
  eager-table suffix timeouts remain resource failures; direct original-code
  lookup passes the small gates. This increment is integrated/audited;
  no secrecy checkpoint is promoted.
  Status: partial. The fair-bit sampler now has checked coin-to-remainder
  execution with derived bounds. `CacheHashCoins.hash` now passes the sampler's
  word directly into insertion and log append on misses, with checked hit behavior
  and a one-request full-source TV bound. The old exact-uniform handler is retained.
  Complete adaptive host-caller correspondence and executed serialized operand
  preparation now check. The sampler and resident cache request have derived combined physical
  execution bounds. Complete adaptive source-caller execution and cost remain.
  `CoinScalarMachine.run_source` now checks uninterrupted coin-to-prefix execution,
  deriving both return-link termination premises and total charge. The guarded
  binary subtraction and one remainder-update program in `BinarySubtractMachine`
  are integrated/audited. Complete loaded-word division now checks in
  `BinaryModuloMachine.run`; its root build, standard-axiom audit and PDF review
  pass. The first two conditions below are integrated/audited; condition 3 has
  checked combined coin loading/division/writing and adaptive host-caller
  correspondence plus serialized operand preparation and the sampler's combined
  physical bound. Resident cache entry/return, complete single-nonce sampling
  and the complete nonce-pair caller are integrated/audited; source arithmetic,
  adaptive continuations and their combined cost remain as detailed below.
  Acceptance, in order:
  1. **Complete:** guarded subtraction and the actual shift/subtract update retain
     the modulus and canonical remainder with a linear bit-cost bound. Evidence:
     `BinarySubtractMachine.run` / `.remainder_step`, six Lean controls, 16,129
     raw pairs, 20 boundaries and 4,160 update fixtures; root build, standard-only
     axiom audit and reviewed reference §14.52/page 69.
  2. **Complete:** `BinaryModuloMachine.run` links
     the existing update into complete division, with derived remainder/width
     invariant and bound N*(8*q.size+13)+2 TM2 ticks. It executes input reversal
     and two return-transfer passes, preserves q, and clears all input/scratch.
     `result_width` bounds canonical output length by q.size. Seven Lean controls,
     16,352 exhaustive cases (raw width 0..8, q=1..32) and 1,500 seeded cases
     (width 0..128, q=1..65536) pass; input-order and return-order mutants are
     detected. This is loaded-word execution, not a free host `%` operation;
     physical coin/modulus loading and scalar handoff remain condition 3. Root
     build, exact-name standard-axiom audit and reviewed reference §14.96/
     Theorem 14.98 (pages 121–122; theorem page 122) pass.
  3. **Partial:** `CoinWordLoader.run_source` executes chronological coin loading
     with 4*w+2 source transitions and exact charge 15*w+9. `.word_index` and
     `.run_modulo` identify its numeric observation with the original sampler
     as an oracle query tree. Five controls and 1,023 exhaustive/1,500 seeded
     fixtures, root build, exact-name standard-axiom audit and reviewed reference
     §14.97/Theorem 14.99 (page 123) pass; this increment is integrated/audited.
     The initial charge
     15*w+8 is refuted by the checked zero-width control. Width and modulus
     are loaded inputs; the modulo theorem is an observation, not division
     execution. That execution link now checks in `CoinModuloMachine.run_source`:
     one fixed program, complete oracle tree and output frame, clock
     (4*w+2)+(w*(8*q.size+13)+3), leaf charge at most
     15*w+9+32*(w*(8*q.size+13)+3). `BinaryModuloCode.tick`/`.run` derive finite
     coordinates for the existing division; `.local_cost` proves its bound 32.
     `load_run`/`divide_run` derive both regions, excluding new coin queries
     after handoff. `.sampler_value` identifies actual produced digits with the
     original modulo sampler. Five controls and 2,032 exhaustive/750 seeded
     fixtures, root build, exact-name standard-axiom audit and reviewed reference
     §14.98/Theorem 14.100 (page 124) pass; this increment is integrated/audited.
     `ScalarWriteCode.run_digits` now reuses the existing prefix writer directly
     on the remainder port. `.from_sampler` derives writer fuel and charge;
     `.sampleWord_source` passes every stack unchanged through a two-phase driver,
     and `.sampleWord_value` matches the original scalar sampler's encoding tree.
     Six controls and 3,840 exhaustive/750 seeded independent fixtures pass.
     Root build, exact-name audit and reference §14.99/Theorem 14.101 (page 125)
     review pass; this increment is integrated/audited.
     `CoinScalarMachine.run_eq` now compiles that boundary into one fixed program,
     deriving source and writer termination from their actual reachable outputs.
     `.run_source` retains the full query tree, frame and charge; `.sampler_value`
     matches the existing sampler's encoded observation. Six controls and
     2,032 exhaustive/750 seeded fixtures pass; the checked live-padding
     counterexample excludes dropping final continuation termination. Root
     integration, exact-name audit of 1,619 public computational theorems and
     reviewed reference §14.100/Theorem 14.102 (pages 125–126) pass; this
     increment is integrated/audited.
     `CacheHashCoins.hash` now implements the word-facing miss/hit handler using
     the actual sampler's encoded output and the existing cache/log routines.
     `.hash_miss`/`.hash_hit` derive complete outputs; `.hash_source` ties the
     comparison to `ballotFiniteLoggedImpl` with the pinned exact-uniform scalar
     sampler. `.hash_distance` bounds the full response/cache/log TV by 2^-slack
     for width=size(q)+slack. Five controls and 576 exhaustive independent cases
     pass, with three detected mutants. Root build, exact-name axiom audit and
     reviewed reference §14.101/Theorem 14.103 (pages 126–127) pass; this
     increment is integrated/audited.
     `CacheCallerCoins.run_eq` now connects every adaptive caller to the original
     finite logged source under the existing fair-bit transformation. The actual
     sampler handles uniform-range requests as well as hash misses; decoding uses
     the returned word. `.source_bound` derives the exact-source query bound from
     the original caller, and `.distance` bounds the complete return/cache/log law
     by B*2^-slack. Five controls and 6,144 exhaustive/300 seeded cases pass,
     detecting hit-resampling, cache-reset and dropped-log mutants. Root build,
     exact-name axiom audit and reviewed reference §14.102/Theorem 14.104
     (page 128) pass; this connection is integrated/audited.
     Next execute width/modulus preparation and physical routine/port transfer,
     then combine the complete caller execution and its derived costs. The new
     full-caller connection still uses host decoding and typed continuations;
     it does not close the physical compilation acceptance condition. The new driver
     still sequences its executed routines through host control; the old exact
     handler and full-source runner are retained as references. Preserve the
     statistical loss and independent controls.
  Priority and closure review (2026-09-14): finish the complete caller connection,
  executed width/modulus preparation and combined execution-cost proof before
  optional infrastructure. Before adding a component, name the obligation and
  explain why current project/pinned-library interfaces cannot discharge it.
  Document each substantial component's interface, assumptions, Helios-specific
  dependencies and potential callers in the existing evidence workflow.
  `SamplerOperands.run`/`.uniform_run` now execute preparation from unary slack
  plus its delimiter and the existing encoded natural. Direct entry requires
  positive modulus q; uniform entry executes the original upper bound t to t+1.
  They preserve suffix/private frame and clear scratch, with derived clocks and
  local charge. `PreparedScalarMachine.run_source` links preparation, a rejection
  gate and the existing sampler in one fixed program. `.within` derives the
  physical compiler contract; `.physical_run` starts from raw input and blank
  work storage using the existing loader/compiler and derived combined cost.
  `CacheHashCoins.hashPrepared` and `CacheCallerCoins.sampleUpper` now use that
  program in the actual adaptive caller; its complete correspondence/error
  theorems and prior controls still pass. Operand, complete-sampler and updated
  adaptive fixture campaigns pass. Root build, exact-name computational axiom
  audit, symbolic claim gate and reference checks pass. Reviewed reference
  §14.103/Theorems 14.105–14.106 (pages 129–130) records this integrated/audited
  sampler component; C6 itself remains partial.
  The complete fixed request now checks in `CacheHashDispatch.request_run`:
  all typed finite cache/key/log inputs have the original complete raw coin tree,
  final answer/cache/log/private records, derived termination and combined charge.
  `miss_run` derives the clean workspace and freshness branch from the probe;
  `hit_run` derives scratch bounds using existing deterministic stack growth,
  then executes both cleanups and the scalar writer. Actual copies, insertion,
  append and all return flags are connected. `.within` supplies the existing
  compiler's contract from this run; `.physical_run` derives execution from the
  loaded twelve-port layout. `.execution_source` matches the existing adaptive
  caller's entire cache-request observation. Seven kernel controls and 324
  directed native fixtures pass; three actual-code mutations are detected.
  Root build, exact-name axiom audit, symbolic/reference checks and reviewed
  §14.105/Theorems 14.108–14.109 (pages 132–134) pass; this loaded-request
  component is integrated/audited.
  This closes the complete request's composition/cost obligation, not C6.
  `CacheRequestInput.load_request` now derives all four caller words from one
  canonical serialized record, with exact scratch cleanup, suffix exhaustion
  and cost. `CacheRequestMachine.request_run` composes it through an executed
  success gate with the complete request. `.physical_run` starts from blank
  physical work storage and a conventional input tape. `.clock_le_loaded` and
  `.cost_le_loaded` derive bounds from payload lengths, public parameter widths
  and slack; no typed cache/log count, intermediate state or cost certificate
  remains an external premise of this one-request interface. Root build, full
  exact-name standard-axiom audit, symbolic/reference gates, eleven kernel
  controls and native loader/wrapper mutation gates pass. Reviewed §14.106/
  Theorems 14.110–14.112 (pages 134–136) is synchronized; this per-request
  increment is integrated/audited. C6 remains partial.
  The request-bound/prefix sub-obligation now has integrated/audited machine-checked
  evidence in `CacheRequestPolynomial`, `CacheRequestPrefixes` and
  `CacheRequestPrefixBounds`: an explicit cubic bound and polynomial-family
  witness; exact original-source erasure and supported execution lifting;
  persistent prestate capture including hits/uniforms; derived encoded storage
  and request execution bounds; historical `n+15` source specialization.
  `requestBound_polynomial` derives codec/header family bounds from public
  modulus widths, count budgets and slack. No intermediate cache/log invariant,
  runtime certificate or source correspondence is an external premise. The
  observation list is analysis instrumentation, not public protocol output.
  Native arithmetic/trace mutation gates and kernel controls pass; root build,
  exact-name standard-axiom audit, symbolic/reference gates and reviewed
  §14.107/Theorems 14.113–14.114 (pages 136–138) pass.
  Exact remaining C6 obligations, in dependency order:
  (1) `CacheCallerMachine.load_request` (integrated/audited): execute entry from an
  explicit enclosing caller layout, preserving saved data and canonical operands.
  Route reviewed 2026-09-14: retain cache/log in the existing dispatcher layout
  and transport changed operands to `CacheHashDispatch.code`. This avoids
  serializing/reparsing the same state on each call. The alternative is four
  source-preserving copies plus `FrameWriteMachine` framing, then the checked
  serialized loader; it is valid but adds redundant executed work. Reuse
  `BitCopyMachine.run`, `BitOracleStackFrame.run` and `BitOracleReturnLink.run`
  for actual moves, saved ports and fixed return labels. The next theorem must
  derive the full entry/frame/scratch state and charge from actual instructions.
  `CacheCallerMachine.load_request` and `.request_run` are integrated/audited:
  exact live dispatcher entry, full original request tree/result, guarded return,
  saved-word preservation and derived combined request charge. `.execution_source`
  matches the existing host request specification; `.source_clock_bound` reuses
  supported-source storage bounds, keeping old-answer length explicit. `.within`
  and `.physical_run` derive the primitive compiler contract/time from the actual
  resident layout, including saved-word height. The 525-case native gate detects
  four actual-code mutations; nine kernel controls include a miss followed by
  reentry on the actual returned configuration. Root build, exact-name standard-
  axiom audit, symbolic/reference gates and reviewed §14.108/Theorems 14.115–
  14.116 (pages 138–140) pass. This closes resident transport, not canonical operand
  production or the complete adaptive-caller obligation.
  Canonical key/operand production by the source remains a C5/C7 obligation;
  naming arbitrary supplied words does not discharge it. The existing raw-input
  request theorem is retained for standalone entry. General malformed payload
  validity is not part of the loader completeness theorem.
  (2) `CacheCallerMachine.run` and `.cost` (planned): execute actual source
  dispatch, response decoding and continuations, then derive the combined
  adaptive caller execution/cost. This depends on the proved request bounds,
  (1) and the C5/C7 effective-caller interface. Arbitrary uniform-range widths
  require that interface's policy; a hash budget does not bound them. Arbitrary
  host functions are not a compilation
  premise. Existing `CacheCallerCoins.run_eq`/`.distance` remain its specification
  and sampling-error evidence. Do not assume a missing correspondence or cost
  certificate. The raw-input one-request component is proved; enclosing record
  construction, canonical decoding and continuation invocation remain open.
  Concrete source continuation: `PrimeNonceMachine.successor_run` now checks
  execution of `uniformNatEncode i.val` to `scalarEncode (primeNonceValue i)`.
  `samplePrimeNonzero` maps this successor over `uniformSample (Fin (q-1))`;
  `drawPrimeNoncePair` and `repairedSubmissionWithNoncePairs` are immediate actual
  callers. It reuses the checked parser, incrementer and writer through the
  existing operand-preparation and scalar-writing components.
  `PrimeNonceMachine.run_nat` and `.charged` execute one fixed program with
  full scratch/frame equality and charge ≤32*(5*n.size+6*(n+1).size+16).
  Existing `SamplerOperands.compiled` supplies parsing/increment, and a fixed
  coordinate map connects the existing writer after width-marker cleanup.
  Root build, six kernel controls and 1,024 native fixtures pass; three actual
  defects shrink to index zero. Root build, full standard-axiom audit and reviewed reference §14.109/Theorem 14.117 (pages 140–141) pass; this successor component is integrated/audited.
  `PrimeNonceMachine.sample_source` now checks the complete serialized-input
  sampler: executed q-to-q−1 preparation, correct decremented width, coins,
  reduction and successor, with full state and derived combined charge.
  `NonceOperands.run`/`.charged` reuse `BitCounterMachine` and the existing
  parser/width region; a scoped instruction-agreement proof justifies the
  changed control. Only the existing layout and width theorem were exposed.
  Saved words are framed outside all eight sampler work ports; the successor
  consumes the returned index directly, preserving modulus and saved data.
  `.sample_execution_source` identifies the exact historical fair-bit query
  tree; `.sample_loss` retains the original one-draw 2^(-slack) loss.
  `.sample_within` and `.sample_physical_run` derive the primitive compiler
  contract and complete physical bound from resident input/frame. No encoded
  predecessor, intermediate frame or runtime certificate is supplied.
  Targeted checks and native/kernel controls pass; root build, full standard-axiom audit and reviewed reference §14.110/Theorems 14.118–14.119 (pages 141–143) pass; this complete single-nonce component is integrated/audited.
  The following pair increment closes `drawPrimeNoncePair` invocation/storage.
  Subsequent honest-constructor operations, effective attacker dispatch and
  total adaptive cost remain open.
  `PrimeNoncePairMachine.pair_run` and `.pair_execution_source` now check the
  actual `drawPrimeNoncePair` caller: resident record copies, first-answer storage,
  work cleanup, two successive sampler calls and the exact joint source tree.
  `.pair_loss` retains the two-draw loss; `.pair_within`/`.pair_physical_run` derive
  combined charge and physical cost, with actual context height explicit. All
  return/frame/nonce-width premises are proved. The 160-case full-pair native
  gate detects four actual-code mutations; nine kernel controls include distinct
  q5 nonces in both orders and exact remaining coins. Transport has its own
  full-state/charge proof and independent controls. Targeted builds pass; root build, full standard-axiom audit and reviewed reference
  §14.111/Theorems 14.120–14.121 (pages 143–145) pass. This pair increment is
  integrated/audited. This closes pair invocation/storage, not the
  subsequent constructor or complete adaptive-caller cost.
  After the pair, `strongHonestBallotWithNoncesOracle` lowers its first proof
  request through `honestProofStatement`/`encryptWith`. Loaded modular
  multiplication, power and both ciphertext coordinates now have actual run,
  source and derived cost proofs under C7. Source-input routing and later
  scalar/proof operations, including nonce addition, remain. The pair theorem
  alone supplies no constructor state encoding or public operand initializer.
  Next concrete routing obligation: `PrimeNonceCiphertextMachine.run`
  (targeted build confirmed; integrated audit pending), extracting the actual first returned scalar prefix into encryption
  nonce digits while retaining both nonce prefixes and the original context.
  Compose with `PrimeNoncePairMachine.pair_execution_source`, not an assumed
  independent nonce source. A scoped 23-port layout maps pair ports to
  [0,22,1,2,3,21,4,5,19,20,14], preserving record19/first20/second21/modulus22
  and leaving encryption's 0–18 layout available. Existing
  `NatPrefixMachine.encoded_run` parses `scalarEncode r` (definitionally
  `uniformNatEncode r.val`); existing copy/frame/return interfaces suffice.
  Its required result includes actual prefix consumption, successful guard,
  empty scratch and derived width/charge, with the prior context preserved.
  The fixed route controller and nine independent kernel controls now check.
  Its 810-case native gate and identical direct-kernel campaign pass across
  seeds118/606/20260914, with six actual-code mutations detected and no discards
  or gaveUp; the native gate also checks eight malformed rejections. The kernel
  campaign checks complete state at 7*n.size+9 ticks and every local instruction
  cost≤6. The general `.run`, `.padded_run` and `.charged` now pass their module
  build with standard axioms. `.charged_bounded` supplies a wider caller clock
  from n≤bound; `.scalar_clock_le` derives the actual scalar's q−1 width. All
  23 ports, scratch cleanup and cost≤6*clock are proved, with padding only after
  final halt. `PrimeNonceCiphertextCaller.caller_run` now proves the actual
  joint two-draw → routing → first-ciphertext execution and derived aggregate
  charge. `.execution_source`, `.within` and `.physical_run` pass targeted
  module builds, retaining every port and both nonce prefixes. Ten independent
  controls and the identical 60-case kernel campaign pass; per-fixture aggregate
  charges were omitted from that campaign and are proved by the general run.
  The redundant interpreter campaign was deliberately stopped after the kernel
  campaign and general cost proof passed; it is not reported as a completed run.
  This physical theorem starts with resident operands. Public p6/g16/pk15 and
  private vote18 now have an independently checked initializer, whose outer
  composition remains the next obligation. `ballotParametersBitCodec`/group codecs supply
  semantic encodings, not that initializer; p/q are parameters rather than
  automatically decoded fields. `RecordParserMachine.total_run` checks framing
  but does not populate these ports. Derive those origins before claiming full
  caller integration. Keeping the private vote in a machine port must not add
  a public observation. An arbitrary preserved context word is not a proved
  encoding of the complete source caller state. Repeatedly serializing the
  arithmetic intermediates would leave these same origin obligations open.
  Source-input audit (2026-09-14): use the actual constructor boundary.
  `repairedSubmissionPrimeSourceOracle` takes g/pk/vote directly and
  `repairedSubmissionWithNoncePairs` passes them unchanged to the honest
  constructor after drawing nonces. `PrimeHonestInputMachine.run`
  consumes existing framing of p, `(ballotCiphertextBitCodec p q).encode (g,pk)`,
  the q/slack sampler record, `[vote]` and saved data. It derives the full
  pair-entry state and input-dependent cost from instructions, preserving the
  original input privately. Existing `RecordFieldStepMachine.field_complete`
  already proves field extraction with exact suffix/output and clean scratch;
  use it with the existing natural-prefix/copy/frame/return routines.
  Parsing the larger `PublicParameters` record is unnecessary at this source
  boundary and would not prove key generation. Whole-election key generation,
  later executed call-site argument transfer, concrete honest return labels and
  C5's effective attacker-state representation remain separate obligations.
  The initializer `.run`, `.padded_run` and `.charged` now pass targeted
  production builds: all ports, raw-input preservation and the input-length
  clock 14*N²+54*N+83 (charge at most 32 times this clock) are derived.
  Its gate passes 28 canonical inputs, 13 malformed rejections, seven detected
  mutations and two typed-codec checks. A retained false test expectation
  shows that bypassing the pk suffix guard still rejects one malformed input
  through later workspace contamination; a separate nested-suffix witness
  detects that same mutation. These components are integrated with the outer
  prefix below.
  `PrimeHonestCiphertextMachine.linked_run` and `.charged` now pass targeted
  builds: initialization, its actual success/reset guard and the joint caller
  execute with original input as private context, at clock initializer.clock +
  1 + caller.clock and derived combined charge. `.execution_source`, `.within`,
  `.start_height` and `.physical_run` also pass the root build; the latter
  includes actual raw-tape loading from blank work, startup≤4*N+8 and physical
  clock unitCost(N+B)*B*globalFactor. The complete exact-name standard-axiom
  audit, symbolic/reference gates and compiled, visually reviewed reference
  §14.115/Theorems 14.128–14.129 (pages 151–152) pass. This prefix is integrated/
  audited; C6 remains partial at 2/3 main milestones and 6/12 checkpoints. Twelve outer full-state cases and five link mutations pass.
  A malformed input rejects before draws; bypassing the guard consumes eight
  coins before later rejection. This closes a first-ciphertext prefix only.
  Current exact source obligation: compose the four full-field c,e,z0,z1
  draws of `ballotFullSimTranscript` and derive their complete raw-input
  caller execution and total cost. The source is
  `repairedSubmissionPrimeSourceOracle` interpreted through
  `ballotFiniteProgrammedImpl`; simulated commitments and `.program` follow
  those four draws. The real prover's three nonzero proof coins are a different
  source path. Existing `CacheHashMachine.sample_run` supplies the full-range-q
  sampler, framed through [1,2,3,4,5,7,8,9,0,17,14,19].
  Targeted production builds now check `PrimeHonestTranscriptMachine.charged`,
  `.execution_source` and `.within`, including zero and every retained port.
  `PrimeFullFieldSource.scalar_word_source` identifies the actual ZMod sampler;
  `.ballotFullSimTranscript_factor` connects the four-draw tuple to the exact
  existing simulator definition. Commitment execution is still outstanding.
  `TranscriptScalarSave.run`, `.padded_run_bounded` and `.charged_bounded`
  derive consuming saves to10/11/12 and clearing of q-workspace on2.
  Its18-case/five-mutation kernel gate and retained controls pass. The local
  first-draw native gate passes11 canonical/eight mutations and guard rejection;
  the earlier29-case kernel campaign remains unpassed after a retained resource
  failure. Kernel positives use the checked general run and literal expected
  states; native validation is not relabelled kernel validation.
  `PrimeTranscriptDraws`' eight-case/four-mutation gate now passes, preserving
  complete states, coin order/residuals and independently derived bounds.
  The no-modulus-clear mutation is a bounded trace/cost counterexample, not a
  claim about eventual nontermination. `PrimeTranscriptDraws.charged`,
  `.execution_source` and `.within` now pass production checks: all concrete
  phases, empty destinations, width conditions and total costs are derived.
  `PrimeHonestTranscriptCaller.linked_run`, `.execution_source`, `.within` and
  `.physical_run` also pass. The actual original input supplies every retained
  word; the exact source is the two historical nonce draws followed by the four
  full-field draws. Startup≤4N+8 and the combined physical execution bound are
  derived, with no supplied correspondence or cost certificate.
  The root build, complete exact-name standard-axiom audit and symbolic/
  reference checks pass. The compiled reference §14.116/Theorems14.130–14.131
  (pages152–154) is visually reviewed; this four-draw raw-input prefix is
  integrated/audited. The smaller raw native campaign passes two p3/q2 cases
  with both votes/coin-word orders and both skip-draw/context-corruption
  mutations. Its singleton nonce space does not test distinct nonce values;
  larger reached-state fixtures remain in the separate four-draw campaign.
  The earlier90s timeout and larger q11/300s timeout returned no mismatches
  and remain unpassed execution attempts. Kernel controls separately check
  exact typed/literal entry and paired full-frame instruction boundaries.
  Durable first/four/raw scripts preserve independent fixtures and original
  instructions; raw defaults to the checked small campaign, while `--larger`
  retains the unpassed larger campaign. CI runs the checked defaults.
  No additional checkpoint closes; no sampler or generic compiler was added.
  Commitment execution follows on these reached scalar/ciphertext words;
  the first-coordinate result below preserves the full transcript/caller frame.
  Remaining coordinates and the programmed-state update must execute before
  the next proof request. These four draws alone do not close a transcript
  or C6. Reuse the checked power/multiply routines and derive actual scalar
  subtraction/negation and operand preparation rather than assuming them.
  Current first-coordinate experiment: use the group exponent q−e.val rather
  than canonical scalar negation. At e=0 this exponent is q, so exact source
  equality must derive alpha^q=1 from actual PrimeGroup membership; retain
  zero/non-subgroup controls. Existing prefix parsing and subtraction produce
  the exponent, then the existing two power calls/product execute the coordinate.
  No canonical-negation or field-inverse routine is needed for this obligation.
  Concrete representation issue: saved transcript scalars overlap the
  power routine's workspace. The scoped comparison selects15 appended private
  work ports (38 total), keeping the original23 fixed. A smaller custom map
  needs more scratch scheduling; packing needs extra serializers/parsers and
  preservation proofs. Existing StackFrame handles this fixed extension.
  The physical proof must use the new controller's own compiler factor and
  actual initial height. No arbitrary-host-continuation compiler is introduced.
  `ScalarComplementMachine`'s general run and actual charge pass after its
  44-case/six-mutation gate. The first-coordinate source identity with q−e and
  nine kernel controls pass. The complete local controller gate passes nine
  full-state fixtures, eight actual mutations and the failure guard; the raw
  caller gate passes one p3/q2 fixture and an actual skipped-commitment mutant.
  `inputWords_source` derives every operand and blank scratch condition from
  the actual four-draw source result. Full local execution/charge and raw
  source/physical composition now pass in production targets with standard
  axioms only. The existing prefix's
  support-bound proof is exposed as `run_support` for the actual combined
  charge; no new cost certificate or correspondence premise is introduced.
  Root build, full standard-axiom and symbolic/reference audits, five checker
  tests and reviewed reference §14.117/Theorems14.132–14.133 (pages154–156)
  pass. This raw first-coordinate increment is integrated/audited; no checkpoint
  closes. The second zero-branch coordinate z0·pk−e·beta must preserve
  the first coordinate and all caller data. The first controller requires
  port3 empty and uses it as scratch, so it cannot simply be called unchanged
  with its first result resident. Compare a fixed operand/workspace remapping
  with a small retained-result frame before adding glue; reuse the checked
  powers/product. The scoped comparison selects a fixed39-port relocation:
  swap local0/17 and15/16 to read actual beta/pk, route local scratch/output3
  to new38, and retain the first result on original3 in the singleton frame.
  This reuses the unchanged numeric controller and adds no executed copies.
  The actual second-coordinate source identity, seven independent algebra
  controls and complete typed input/output presentation pass. Local/raw code
  gates and the full PairCaller charge/source/physical composition now pass.
  Root build, full standard-axiom and symbolic/reference audits, five checker
  tests and reviewed §14.118/Theorem14.134 (pages156–157) pass: the zero-branch
  pair is integrated/audited, with no checkpoint closure. Next complete the remaining
  branch and statement/programmed-state construction. For that branch the
  exact remaining operands are canonical d=c−e, z1 and beta−g. Feeding q−e
  directly as a reduced operand fails at e=0; retain the counterexample and
  prove zero-safe modular subtraction. Inspection identifies a narrower route:
  the unchanged BinaryModAddMachine already accepts c.bits/e.bits/q.bits.
  Extend its proof with `difference_run` and `difference_charged`: use the
  existing theorem with x=q−e for e>0, and prove the actual subtract/finish
  path separately at e=0. Both use the existing clock26*q.size+24 and
  charge32*clock. This does not assert q−e<q at zero or add a controller.
  The full-state endpoint/c<e/c=e gate passes1730 cases and five mutation
  checks. The general extension, typed source and three direct kernel controls
  pass in the existing production Run module with standard axioms; this is
  integrated/audited evidence. Actual pair-state operand routing and cost execute: copy/parse existing U(c)/U(e), execute
  that difference, write U(d) with the existing prefix writer, and clean work.
  Keep both old coordinates and all inputs, using empty port1 for U(d) and
  existing work23–37. The narrow finite controller's code gate, general
  execution/source/charge and direct kernel controls pass. Actual39-state
  input/output presentation and local source/charge pass. The raw gate
  retained a300s resource timeout and passed unchanged code/model caps
  with600s host allowance. Raw general source/physical composition also
  checks. Root build, complete standard-axiom and symbolic/reference audits,
  five checker tests and reviewed reference §§14.119–14.121 pass; the full
  all-commitment increment is integrated/audited.
  Existing FrameWriteMachine supplies
  the scalar-prefix writer after the actual d digits are produced. Port7
  already holds z1's prefix and port22 already holds (q−1).bits for the
  existing power/product construction of beta−g. Source identities/controls
  and that port22 fact check in production. For adjusted beta−g, the selected fixed
  Power/Multiply maps read the retained operands directly, consume inverse23
  and write a new output39 while retaining d-prefix1/A3/B38. This avoids the
  extra constant-prefix setup and extra power of a full commitment-controller
  reuse. Its local code gate, numeric run/charge and actual typed
  presentation/source now check. The full raw composition below includes it.
  Both one-branch coordinates execute via the unchanged543-label numeric
  controller: first fixed42-port map reads d1/z1-prefix7, preserves A3/B38/gamma39
  and writes40 with scratch41; second43-port map reads pk15/gamma39 with d1/z1,
  retains earlier outputs and writes42. Both independent reached-state code
  gates and full source/frame/charge proofs now pass. PrimeSimOneTail derives
  the complete gamma+one-branch execution; PrimeSimAllCommitCaller connects
  it to the actual raw difference prefix, deriving all four original commitment
  coordinates, the unchanged complete source tree and total physical cost.
  Independent full43-state final controls pass; kernel label/return checks and local actual-code
  gates validate composition boundaries, without claiming another full raw
  native campaign. All public source correspondence must be derived.
  First-key serialization now checks from reached ports 16/15/17/0/3/38/40/42.
  PrimeSimKeySource derives their canonical digits and the exact existing
  flat eight-field codec. NatFieldWriterMachine reuses copy and the existing
  prefix/full-field writers; PrimeSimKeyMachine executes eight invocations
  and the fixed count prefix, with full retained state and derived charge.
  Independent single-field and full-key code gates, typed source and literal
  controls pass. PrimeSimKeyCaller derives exact original raw-source and
  physical execution with its own combined code factor. Root build, complete
  standard-axiom and symbolic/reference audits, five checker tests and reviewed
  §14.122/Theorems 14.139–14.141 pass; this increment is integrated/audited.
  No checkpoint closes. The standalone key caller allows arbitrary saved bytes.
  The integrated state extractor specializes them to the original typed-state
  codec and derives the resident shadow/live/flag/history presentation.
  Its complete run and charge are integrated/audited: BitCopyMachine and eleven
  existing FieldPrefix calls unpack retained raw 14
  into appended shadow/live/flag/history ports 44–47, preserving the prior 44
  words and clearing work 23–27. Its clock has a derived quadratic raw-size
  envelope. Actual raw caller integration derives the unchanged source tree,
  retained state and combined physical bound. Root build, complete audits,
  independent controls and synchronized §14.123 pass.
  The nested presentation is derived from the typed codec and exact original
  first request for arbitrary finite shadow/live states. That semantic origin does
  not by itself execute enclosing serialization; predecessor construction and
  successor repacking remain required. The occupied full-state audit confirms
  residual insertion work 0/4/5, so capture collision before clearing it.
  Extraction is complete. The existing ballotBothCachesBitCodec's executed
  repacking and enclosing predecessor/successor serialization remain open.
  The local transition components and source interfaces now pass targeted
  checks. PrimeProgrammedInsertInputMachine copies shadow44 to23 and clears44;
  its full arbitrary-frame run and uniform padded charge use only the derived
  empty work and cache-word length. CacheProgrammedInsertMachine reuses the
  original insertion, captures collision before clearing residue23/27/28 and
  executes the sticky flag. PrimeProgrammedHistoryMachine builds the actual
  nested statement from beta0/alpha17/pk15/g16, parses/increments history47's
  count and prepends in place. Source specializations derive every loaded
  operand, work23–29, input-size bound and actual charge; the resulting
  cache44/flag46/history47 agree with the original state.program, and live45
  and unrelated words are preserved. Component native/kernel gates pass.
  PrimeProgramMachine.charged_source now connects all components.
  PrimeProgramCaller.linked_run, .execution_source, .source_state, .within and
  .physical_run derive the original raw-source tree, complete state successor
  and physical bound. The root build, complete standard-axiom, symbolic and
  reference audits, checker tests and reviewed §14.124/Theorems 14.145–14.147
  pass; this increment is integrated/audited. No checkpoint closes.
  Returned-proof and updated-state encoding are now integrated/audited.
  BitPairWriterMachine reuses existing copy/field writers while retaining both
  inputs. PrimeProgramProofSource derives the original proof fields;
  PrimeProgramRepackSource derives enlarged storage bounds and saved_changed.
  PrimeProgramOutputMachine.run/.charged executes all fixed codec nodes and
  cleanup; .charged_source supplies every operand/workspace/bound premise from
  the actual preceding source. PrimeProgramOutputCaller.linked_run,
  .execution_source and .physical_run connect the original raw input to exact
  proof48/saved49, retaining all 48 prior words and the unchanged draw tree.
  Both native gates, independent typed controls and the root build pass.
  Complete standard-axiom and symbolic/reference audits, checker tests and
  reviewed §14.125/Theorems 14.148–14.150 pass; this increment is integrated/audited. Original raw14
  still contains the predecessor saved state: re-extracting it would restore
  stale values. A successor must consume the updated resident fields or their
  executed re-encoding, and derive bounds for the enlarged cache/history.
  The original ballotTranscriptProof now executes through ballotProofBitCodec.
  Next execute the resident p1 and pt continuation, preserving
  the sampled nonce pair and allowing its modular sum to be zero, then Bob's
  construction, verification, attacker and final submission continuations.
  The resident second-ciphertext/four-draw prefix now passes complete targeted
  checks and the root build. PrimeRemainingProgramSource.continuation_run exposes
  the exact two remaining Alice requests and state threading. The source
  presentation/work/nonce/length lemmas derive the retained second nonce,
  updated saved state and all local operands. PrimeSecondTranscriptMachine.charged
  derives actual routing, false-vote encryption, four fresh words and summed
  charge; MachineSource.execution_source/run_support_source derives the typed
  fair-bit tree and every supported return. PrimeSecondTranscriptCaller
  linked_run/execution_source/physical_run connects one original raw input to
  that complete prefix, retaining the first proof and nonce pair. No stale raw
  context is re-extracted or nonce resampled. The instruction gate is complete
  across retained directed/mutation results and the successful isolated seeded
  retry with unchanged code/model caps; typed endpoint controls pass. Complete
  audits, five checker tests and reviewed §14.126/Theorems 14.151–14.153
  (pages 168–170) pass; this increment is integrated/audited. Next execute p1's commitments,
  programming update and proof return, then the overall request (including
  the possibly zero modular nonce sum), later ballots, verification and attacker
  execution. The fixed map reuses numeric/frame machinery; the first-call outer
  source theorem cannot be repurposed by renaming its witness while retaining
  stale raw14. No checkpoint closes at this prefix boundary.
  The first p1 commitment now passes targeted resident and raw-caller checks.
  PrimeSecondCommitSource derives fresh e1/z01, second ciphertext, numeric bounds
  and complete input/output frames from the actual preceding result. The fixed
  65-port map reuses PrimeSimCommitMachine unchanged and preserves all old59
  words; charged_source derives actual execution and its original bound.
  PrimeSecondTranscriptCaller.source_support extracts both source tuples;
  PrimeSecondCommitCaller.linked_run/execution_source/physical_run derives the
  original raw tree, successful returns and summed physical cost. The complete
  native gate passes9 canonical cases/8 instruction mutations/1 rejection with
  seeds118/606/20260914 and no discards/gaveUp. Independent typed controls pass.
  Root build, complete audits, checker tests and reviewed reference §14.127/
  Theorem14.154 (pages170–172) pass; this increment is integrated/audited. The following
  continuation supplies the other three p1 coordinates; key/state programming and proof return,
  overall proof, later election execution and adaptive costs remain required.
  Completed continuation experiment: execute B, canonical d=c−e, adjusted beta,
  C and D under fixed resident frames, then compose one remaining tail and one
  original raw caller. Component gates precede their execution proofs; every
  operand/frame/return and summed charge must be derived. Reuse the existing
  arithmetic controllers unchanged; no separate raw wrapper per coordinate.
  B, canonical difference, adjusted beta and C now have targeted checked source
  execution/charge, with their full instruction gates passed. All five source
  frame presentations and the combined endpoint/retention/return facts pass.
  D's instruction gate and runtime specialization now pass. The aggregate
  PrimeSecondCommitTail.charged_source/execution_source derives all five stages
  and their summed cost (second-commit-tail-runtime-build2.log, standard axioms).
  PrimeSecondAllCommitCaller linked_run/execution_source/physical_run now passes
  from the original typed raw input, retaining the complete source tree and
  all70 endpoint words with the actual combined code factor. The root build
  passes (second-all-commit-root-build.log); complete computational/symbolic
  audits, five checker tests and reviewed §14.128/Theorem14.155 (pages172–173)
  pass. This increment is integrated/audited; no checkpoint closes. Next: p1 key serialization, current-state programming
  and returned-proof encoding, then overall proof and later election execution.
  The second key now has targeted complete source, resident execution and raw
  caller proofs, with unchanged numeric serializer/cost. The native gate passes
  7 canonical/9 actual mutation/1 rejection cases and independent full71 typed
  controls pass. All old70 words are retained; the exact original flat key is
  appended on70. Root build passes; complete integration audits and reference review
  are pending. PrimeSecondProgramSource now derives the required next inputs
  and growth bounds from resident current cache44/live45/flag46/history47,
  rather than reparsing stale raw14. Current count bounds use N+1; original
  source programming branches and semantic successor counts≤N+2 are checked. The actual
  second programming update and returned proof still need execution/cost proofs.
  No complete adaptive cost or standard-PPT coverage follows from one update.
  Preserve the arbitrary-state scope at successor calls; an initial empty-state
  specialization does not discharge that obligation. The statement
  history uses a nested-pair codec, distinct from the flat key; it prepends and
  preserves duplicates. Existing chronological LogAppendMachine is not this
  operation. CacheInsertMachine.programmed_cache_run alone proves cache/flag
  readout correspondence. The new wrapper derives actual collision capture and
  cleanup from its full hit-state theorem and existing clear loops. Sampled c
  on 10 and the key on 43 are preserved, with the surrounding source state
  derived from the actual caller.
  `.program` must preserve sticky
  collision behavior (occupied key sets bad even if its challenge agrees),
  shadow/live cache distinction and duplicate programmed history. Existing hash
  miss dispatch does not execute that update. The required canonical challenge subtraction and adjusted-base inverse
  now execute. C7 still covers later scalar/nonce arithmetic, including
  nonce addition that may produce zero.
  Structural dependency confirmed: C6 closure needs C7's subsequent actual
  group/scalar arithmetic and key construction, plus C5's effective attacker
  interface. Those premises cannot be closed by another sampler/caller wrapper.
  Physical caller compilation must target the concrete finite-control routines.
  Arbitrary `OracleComp` continuations in the semantic correspondence theorem
  are host functions and have no general effective compiler. Reify the actual
  cache/sampling dispatch and explicit return labels in the existing machine
  interface; retain the typed caller theorem as its specification. A new compiler
  for unrestricted host functions would require a different, unjustified claim.
  At C6 closure, review C5/C7/C8/C9/C12 for architectural uncertainty, the smallest
  next obligation and the evidence needed for acceptance. Report any structural
  obstacle earlier with concrete alternatives; derive correspondence and costs
  rather than accepting certificates for the missing proofs.
  Dependencies: C3; interface integration uses C5. The local arithmetic proof
  can proceed before C5 closes; a new general backend cannot.

- [ ] **C7 — Execute remaining protocol arithmetic and saved contexts.**
  **Current disposition: deferred machine-efficiency work.** The following
  partial results and original acceptance conditions are retained as evidence,
  not active prerequisites for the revised deliverable. The semantic width
  guarantees needed for attacker coverage are now checked in C12.
  Status: partial; loaded multiplication, exponentiation and ciphertext
  execution/cost are checked. Source routing, remaining scalar/proof operations
  and complete saved-context execution remain open. Acceptance:
  concrete group/scalar operations, initial/public operand loading, saved replay
  context handling and effective continuation execution have derived bit bounds,
  runtime correspondence and costs. Reuse C4/C6; do not serialize an entire
  branching OracleComp tree or infer local costs from query counts.
  `BinaryModMultiply.run` now checks loaded coordinate multiplication from
  canonical x.bits/p.bits and an arbitrary little-endian multiplier word, x<p.
  It executes p-x preparation, reversal, every doubling/addition and cleanup,
  retaining original x/p with all work cleared. `.charged` derives charge at
  most 32*(9W+11+L*(34W+38)); `.clock_le_product` bounds this clock by
  38*(L+1)*(W+1). `.group_coordinates` connects this loaded execution to
  `primeGroupCoordinate_add`, and `.within`/`.physical_run` derive actual
  primitive execution from its resident ready state. Root build, full standard-axiom
  audit and reviewed reference §14.112/Theorems 14.122–14.123 (pages 145–147)
  pass; this multiplier increment is integrated/audited. The 792-case native gate detects
  five actual-code defects; the inner addition gate checks 1,808 cases and four
  defects. Independent arithmetic identities/controls are retained.
  The prepared-complement premise of `BinaryModAddMachine.run` is discharged by
  the actual outer preparation, not supplied by the source caller.
  The immediate source request is `ballotRealRequestImpl` →
  `honestProofStatement` → `encryptWith`; `primeGroup_encrypt_coordinates`
  requires powers and multiplication modulo p, not scalar modulus q.
  `BinaryModPower.run` now checks square-and-multiply from canonical base/p
  and arbitrary little-endian exponent/context words, with p≥2 and base<p.
  Every copy, reduced accumulator, operand width, frame, guard and cleanup
  premise is derived. `.charged` proves the candidate clock and charge;
  `.clock_le_product` bounds the clock by80*(L+1)*(W+1)^2.
  `.group_coordinates` connects loaded execution to `primeGroupCoordinate_smul`
  for historical prime p and q≠0; `.physical_run` derives primitive execution
  from resident ready state, retaining actual context height. Root build,
  full standard-axiom audit, the 451-case/six-mutant native gate and kernel
  controls pass. Reviewed reference §14.113/Theorems 14.124–14.125
  (pages 147–149) is integrated/audited. Arithmetic refutation controls and high-zero padding remain.
  `PrimeEncryptMachine.run` now checks the concrete two-power caller, saved
  first coordinate and conditional vote multiplication, with complete state and
  the original derived clock. `.source` matches both actual `encryptWith`
  coordinates under prime p/q; `.physical_run` derives primitive execution from
  resident state. The 210-case native gate and nine full-state kernel controls
  pass, retaining seven actual-code defects. Root build, full standard-axiom
  audit and reviewed reference §14.114/Theorems 14.126–14.127
  (pages 149–150) pass; this loaded ciphertext component is integrated/audited. No caller correspondence or cost certificate is assumed. Next:
  execute public-record/nonce-prefix routing from the actual prior nonce-pair
  output, then proof-request encoding.
  Resident digits alone do not discharge parsing or source operand production.
  Existing copy, finite-coordinate and return/frame routines are reused.
  Ordinary product-then-division is an alternative but requires new full-product
  and carry machinery. Iteration once per exponent value cannot establish
  polynomial bit complexity. Preserve p/q separation; independent encryption
  fixture p23/q11/g2/pk4/r3 gives (8,18) for false and (8,13) for true.
  Dependencies: C3–C6, with independent arithmetic work possible earlier.

- [ ] **C8 — Establish quantitative machine adequacy and reduction efficiency.**
  Status: open, deferred as the stronger machine-checked efficiency tier by the
  2026-09-15 closing-audit goal. The revised endpoint permits the explicit
  `MainReductionEfficient` / `RejectionReductionEfficient` hypotheses with the
  documented external argument; this does not discharge C8. Original acceptance:
  lower the concrete protocol/simulator/extractor
  execution to the stated standard probabilistic polynomial-time model,
  preserving complete output laws/observations with the explicit sampling loss,
  and derive polynomial local, query and operand costs. The theorem must cover
  the actual algorithms, not an assumed compilation certificate or only
  `IsOraclePPTBy`. Dependencies: C5–C7 and the integrated algorithms of C9–C11.
  This checkpoint closes only when those algorithms' final costs are covered.

- [ ] **C9 — Integrate the shared-oracle full-election privacy game.**
  Current disposition: the secrecy game and `Family` coverage are checked; further
  historical positive-attack transport is a separate validation extension. The
  following earlier partial status is retained as provenance.
  Historical status: the `BallotAdversary` interface uses ProbComp and
  `repairedBallotSecrecyGame` takes explicit hash functions. Acceptance: one
  shared oracle covers public key/ballot/trustee proofs and attacker queries;
  challenge admissibility, corruption, schedule, tally disclosure, rejection,
  freshness, wraparound and election-size scope are explicit and preserve the
  intended theorem. Existing attack/repair instances must still be derived.
  Dependencies: C1–C3. Specification/integration work can proceed without
  waiting for every low-level arithmetic proof; final efficiency uses C8.
  Checked component: `ElectionOracle.prefix_function` / `.finish_function`
  preserve the complete original public records under fixed hashes;
  `.world_function` / `.game_function` extend this to the actual sampled game
  with interpreted stateful oracle callbacks. `.preparedGame_function` and
  `.run_preparedGame` preserve pre-election state/cache through later phases;
  `.run_repeat` derives repeated-query consistency. `randomGame` starts one
  empty private cache and returns only the winning bit. Nine independent Lean
  controls cover literal contexts/transcripts and mixed hit/miss behavior.
  The fixed three-voter/two-candidate/one-trustee schedule is preserved. General
  challenge/corruption/election-family policy and historical positive-attack
  oracle transport remain open; full adaptive extraction is now discharged by C10; C9 and the checkpoint count do not
  close. Integration evidence is recorded in the results ledger.
  Integrated/audited: root build, standard-only public axiom reports, independent
  fixture and reviewed formal reference §14.53/pages 70–71 all pass.
  Further checked component: `ElectionCache.liftBallot_run` derives exact
  projection/reconstruction from arbitrary full initial caches, preserving the
  other proof domains. `.world_eq_samplePrefix` factors the actual original
  world, and `.preparedPrefix_rejection_le` bounds its honest-prefix rejection
  after arbitrary pre-election queries by `9 * noncePointBound F`; generator
  injectivity is explicit. The 101-element full-prefix control has positive
  acceptance, excluding an always-aborting/rejecting implementation. C10 now connects programmed simulation and the full attacker continuation
  to actual extraction; this earlier component alone did not establish it. Integration details are in the results ledger.
  This further component is integrated/audited: root build, public axiom audit,
  independent controls and reviewed reference §14.54/page 72 pass. That earlier increment left C9/C10 partial; C10 is now discharged below.

  C9 repair-control transport now checks in `ElectionRepairControl`:
  `repairedAttackWithCoins_rejected` and `repairedAttackWorld_rejected` derive
  probability-one reusedCiphertext rejection under the actual shared oracle
  from every initial cache. Exact fixed-hash execution/world correspondence
  preserves all public fields and the original neutral-proof/aggregate reuse.
  Six Lean controls and 240 independent multiplicative executions cover cache
  hits/misses, honest acceptance/rejection and invalid-proof priority. The pinned
  VCVio probability-one bridge supplies the transfer; no new cache machinery is
  needed. Historical positive-attack transport and family policy remain open.
  Integrated/audited: root build, exact-name standard-axiom audit and reference
  §14.75/Theorem 14.77 (pages 100–101; theorem page 100) pass. Counts remain
  2/3 main milestones and 6/12 checkpoints; see the results ledger.

- [x] **C10 — Extend simulation/extraction to the full adaptive interaction.**
  Status: finite protocol obligation completed; root build, controls and
  exact-name axiom audit pass. The reviewed reference §14.74/Theorem 14.76 (pages 98–100, theorem on page 99) is synchronized. Acceptance
  is discharged for the fixed historical three-voter/two-candidate/one-trustee
  scope, including every accepted adversarial submission allowed by that game:
  - Shared-oracle reconstruction and earlier/interleaved queries:
    `ElectionReplaySource.lower_run`, `ElectionProgrammedSource.prepared_runtime_eq`,
    `ElectionDDHSource.prefix_inv` and `.prefix_live` derive runtime/state/cache
    conditions through the actual preparation and casting callbacks.
  - All component/aggregate statements and simultaneous witnesses:
    `.prefix_repeated_valid`, `.prefix_repeated_consistent` and the underlying
    three-witness replay theorem derive distinct challenges, actual cached
    statements, context binding and consistent recovered witnesses. The former
    generic placeholder `strongBallot_adaptive_extract` is superseded by these
    actual-election declarations, not assumed as an additional premise.
  - Fixed original execution and accumulated failure:
    `.prefix_repeated_original`, `.prefix_failure_le` and
    `ballotReplay_parameters` retain every original/failure branch and give the
    explicit accuracy request with k=3456(N+1)^3e^4.
  - Source-derived finishing, rejection and complete comparison:
    `.prefix_honest_columns`, `.prefix_cast_board`, `.extracted_finish_accuracy`,
    `.prepared_real_distance_le`, `.honestReject_real_le` and
    `.honestReject_random_le` discharge the board, freshness, witness and
    real/random rejection premises; no caller supplies correspondence.
  - Integration: `.prepared_ballot_secrecy_ddh_bound` now composes every finite
    loss with the actual complete original game; `.ballotSecrecy_prime_cost`
    derives the matching complete uniform-index query cost.
  Dependencies: C1–C2 and C9's implemented fixed shared-oracle game. C9's family
  policy and known-control transport remain separate. C8 retains pure-operation
  costs and standard-PPT execution; no machine-adequacy result is claimed here.
  Independent controls, the failed semantic-realization shortcut and prior
  incremental evidence remain in the results ledger and formal reference.

- [x] **C11 — Prove the complete ballot-secrecy game reduction.**
  Status: finite advantage obligation completed; root build, six new controls
  and exact-name axiom audit pass. The reviewed reference §14.74/Theorem 14.76 (pages 98–100, theorem on page 99) is synchronized.
  `ElectionDDHSource.ballotSecrecyDistinguisher` runs the actual public-input
  extracted game and returns its winning bit, with no secret or success filter.
  `.ballotSecrecy_real_gap` and `.ballotSecrecy_random_gap` average the actual
  comparisons in both pinned DDH experiments; `.completed_random_win` supplies
  the exact one-half ideal endpoint, retaining every public/trustee/rejection
  observation and arbitrary callbacks.
  `.prepared_ballot_secrecy_ddh_bound` proves the original prepared game's bias
  ≤18/(q−1)+3L+2/e+D_main+D_reject, where L=(11p+2c+131)/q. Its explicit
  premises are scalar-action injectivity, preparation/casting all-proof-hash
  bounds p/c, e>0 and 12(p+c+10)e≤q, with the existing finite-field/module/
  sampling instances. Both D terms are actual two-game DDH advantages. The
  original game's winning projection and every real/random comparison are
  derived, not assumed. `.ballotSecrecy_prime_cost` gives the same algorithm's
  polynomial uniform-index query bound from complete callback budgets P/C/D.
  The q=65537,p=2,c=1,e=16 querying control has explicit non-DDH allowance <1/2;
  it makes no DDH hardness assertion. All six controls and 19,683 independent
  probability-chain cases pass; seven omission/factor mutants are detected.
  Dependencies: C9's implemented fixed game and C10; algorithmic efficiency is
  discharged jointly with C8. This finite reduction does not assert negligible
  DDH advantages or discharge C12's parameterized all-PPT theorem.

- [x] **C12 — Scoped parameterized secrecy under the revised boundary.**
  Status: `Family.ballot_secrecy`, complete source coverage and the explicit
  external-efficiency/strict-PPT boundary are checked and documented. Publication
  validation and synchronization are recorded in the completed package item below. Acceptance: quantify over the intended PPT attackers, security
  parameters, group/election families and stated corruption policy; turn the
  concrete bound into negligible advantage with explicit assumptions and no
  missing source or attacker-coverage correspondence. The revised boundary
  permits named efficiency hypotheses for the exact reductions, justified by
  the external argument; no other acceptance condition is relaxed.
  Audit the public theorem and independent
  controls, run required builds/axiom checks, and synchronize README, results,
  blueprint and PDF at the subsequent publication increment. Dependencies: C11,
  C5/C9 coverage and the explicit external efficiency boundary, retaining C3's
  sampling loss. C8 remains required for the stronger fully mechanized tier.
  This closes the Step 3 proof milestone under the revised boundary; the publication
  goal also requires the synchronized package and verified push.

  **Earlier closing-audit outcome (2026-09-15; coverage superseded below):**
  `ElectionSecrecyConditional.prepared_negligible_of_native_coin_ddh` checks the
  original bias conclusion from the unchanged family/query/field premises,
  named exact-family execution predicates and DDH for the same finite fair-coin
  machine class and representation. Main covers every fixed accuracy degree.
  Root build, targeted statement/control checks and full computational axiom
  audit pass with standard axioms only. The
  [external argument](docs/research/helios-computational-closing-audit.md) covers
  both reductions, including callback configurations, persistent stores, replay,
  guessing, fair-bit sampling and uniform computation of the actual `D.p+D.c`.
  It does not construct Lean efficiency witnesses or close attacker coverage.
  `EfficiencyInputControls.no_uniform_input_cap` refutes an input-independent
  cap for the given input-linear callback; it does not refute normalization.
  The smallest missing `ElectionSecurityFamily.coverage` obligation is a
  law-preserving translation of intended PPT attackers into `PreparedFamily`
  satisfying its global hash/total query caps. It needs reached-input width
  bounds and a clocking/normalization correspondence, or a proved
  support-sensitive formulation of the bounds. The accepted fixed game remains
  three voters, two candidates and one honest trustee; larger elections and
  arbitrary corruption/schedules are outside that case-study scope. Historical
  positive-attack oracle transport remains a separate C9 validation obligation.
  No further proof construction is authorized by this bounded audit itself.

  `ElectionSecrecyPrototype.prepared_negligible_of_ddh` now links the exact
  finite bound to negligible original prepared-game bias. `accuracy_admissible`
  derives the field-size constraint eventually; `replay_bounded` bounds the
  actual replay count by a polynomial for every fixed degree k, with
  e(n)=(n+1)^(k+1). Premises: generator injectivity and actual preparation/casting
  hash bounds in `PreparedFamily`, polynomial combined budget, negligible
  reciprocal (|F|-1), negligible `mainAdvantage D k` for every k and negligible
  `rejectionAdvantage D`. No runtime/coverage claim is hidden in the family.
  Four controls and 3,000 independent arithmetic fixtures, root build,
  exact-name standard-axiom audit and reviewed reference §14.94/Theorem 14.96
  (pages 119–120; theorem page 120) pass; the conditional prototype is integrated/audited. The fixed-linear-accuracy shortcut is refuted by
  `ElectionSecrecyPrototypeControls.fixed_accuracy_not_negligible`.

  Prototype-to-final dependencies (remaining proposed declarations are unproved):
  - `ElectionSecrecyEfficiency.main_ppt` and `.rejection_ppt`: prove polynomial
    local/query/operand/runtime bounds for the exact two DDH algorithms; the
    main family uses each fixed degree k. Depends on C5–C8, not only replay count.
    These proposed machine-proof declarations remain unproved and are deferred
    under the revised boundary; the named efficiency hypotheses do not prove them.
  - **Probability-law sampling transport: checked** in
    `ElectionSecrecyFairBits.prepared_negligible_of_fair_bits`, discharging the
    planned `ElectionSecrecyEfficiency.sampling_transport` at the OracleComp
    level. `ElectionDDHFairBits.real_distance` / `.random_distance` retain exact
    DDH challengers and bound each full output law by B*2^(-slack);
    `.advantage_distance` retains both errors. `.negligible_of_bits` proves
    negligible total loss for slack=n and polynomial B. The actual family
    theorem derives both reduction budgets from existing full query-cost
    theorems and polynomial preparation/casting/guessing bounds. Five controls
    and 750 independent finite DDH enumerations, root build, exact-name
    standard-axiom audit and reviewed reference §14.95/Theorem 14.97
    (pages 120–121; theorem page 121) pass; this increment is integrated/audited.
    C6's effective modulo/coin execution, C7 operand bounds and C8 local/runtime
    costs remain open. The remaining hardness premises concern the exact
    fair-bit reductions; no standard-PPT inference follows from query counts.
  - **Coverage checked:** `ElectionSecurityFamily.Family.coverage` (also exported
    as `ElectionSecurityFamily.coverage`) constructs the clocked family and
    preserves the original complete oracle computation. `.run_coverage` retains
    the final shared cache for every starting cache; `.bias_eq` retains the
    original bias. Input-dependent query and private output-growth premises use
    actual injective encodings; global caps and game correspondence are derived.
  - `ElectionSecrecy.prepared_ballot_secrecy`: apply explicit DDH hardness to
    those efficient reductions and discharge the prototype premises; retain
    historical attack/repair controls and run the final integrated audit.
    Discharged at the revised formal boundary by
    `ElectionSecurityFamily.Family.ballot_secrecy`, which composes coverage with
    `prepared_negligible_of_native_coin_ddh`. The final scope/assumption audit
    and publication package remain outstanding.
  The remaining proposed names identify obligations, not existing declarations.

**Completed bounded proof task: attacker coverage (90-minute limit).**
The attempt stopped at the checked composed theorem, within the authorized
13:12:01–14:42:01 UTC window on 2026-09-15. Exact evidence and the external
membership argument are in the
[coverage outcome](docs/research/helios-results.md#encoded-attacker-coverage-and-composed-secrecy-2026-09-15).

- [x] Establish the complete callback-input width requirements: public records,
  fingerprints and scalar/group encodings, plus private `Init`/`Saved` state
  passed through preparation and casting. Derive game-side bounds where possible;
  identify remaining implementation assumptions explicitly. Query bounds alone
  do not bound pure computation, output sizes or saved state.
- [x] Specify polynomial input-dependent query bounds using the existing
  `IsQueryBound` machinery, together with the required reachable-state width
  guarantees. Explain how intended PPT implementations meet this interface under
  the documented external assumptions. Do not assert coverage merely by defining
  a restricted class; identify any additional restriction or missing argument.
- [x] Inspect pinned VCVio for query-capping machinery and reuse it if suitable.
  Construct clocked callbacks; prove global parameter-only total/hash query caps
  and agreement with the original callbacks on every reached input. Account for
  preparation and the state passed from casting to guessing.
- [x] Prove `ElectionSecurityFamily.coverage`: construct the clocked
  `PreparedFamily` and preserve the original public game distribution, hence
  its bias. Compose with `prepared_negligible_of_native_coin_ddh` to state the
  theorem over the intended attacker class, keeping every cryptographic,
  parameter and efficiency assumption explicit.
- [x] Retain `no_uniform_input_cap`; add independently justified controls for
  truncation on an over-wide input, agreement on reached inputs, and exclusion
  of a callback violating its declared polynomial query bound. Run targeted
  builds and axiom checks; record one outcome here and in the results ledger.

**Outcome and exact boundary:** `Family.ballot_secrecy` concludes negligible
original-game bias from the resource interface, field-size negligibility, DDH
under the chosen representation, and `MainReductionEfficient` /
`RejectionReductionEfficient` for the **exact clocked family**. It does not
transfer efficiency merely from game equality. Prefix/result bit encodings are
injective, preserve all existing fields and specialize to the previous prime
codecs; their length bounds and the actual board/decoded bounds are checked.
Private `Init`/`Saved` sizes are lengths of injective encodings, with separate
callback output-growth bounds. Main's query/replay budgets use explicit derived
polynomials. No machine/backend implementation or C8 completion is claimed.

The external interpretation uses uniformly polynomial-clocked strict oracle-PPT
callbacks, charging index writing, reply handling and output serialization on
all typed reply paths. This supplies local resource premises, not an assumed
Lean game-correspondence theorem. A runtime guarantee only for consistent-oracle
executions does not directly imply these all-path premises; representing an
arbitrary pre-existing such program requires an explicit clock-normal-form
argument. That distinction is retained in the evidence and must not be silently
erased in the final scope audit. No Lean standard-machine characterization of
PPT is claimed. The targeted aggregate build and exact-name axiom audit pass
with standard axioms only; existing proofs and efficiency hypotheses are unchanged.

**Stop rule:** stop within the bound at the composed theorem or a concrete
obstruction, with exact remaining obligations. A theorem conditional on an
unproved attacker-coverage correspondence does not close this task. Do not
automatically expand into a backend, compiler, general framework or a new
infrastructure track. Leave the efficiency hypotheses, C8 and historical attack
transport unchanged. Defer PDF regeneration and publication during the attempt.

**Closing work after coverage:** the fixed-game scope and all assumptions are
audited; the root build and axiom/document checks pass, and the synchronized PDF
has been visually reviewed. This is verification and publication, not another
proof-development track. Main position is **3/3 proof milestones complete under
the revised boundary; publication package complete**. The publication record in
the results ledger carries the exact evidence and preserved limitations.

- [x] Prepare and validate the case-study publication package: exact theorem and full `Family` transcription,
  complete assumptions/external-argument audit, declaration-backed scope comparison,
  verified experience report, synchronized README/blueprint/models/results/PDF,
  root build and audits, all-page visual review, committed PDF and verified push.
  Preserve C5–C8 TM code; no module removal, Lake split or transfer work in this task.

**Publication cadence (user steering, 2026-09-14):** commit and push each
substantial integrated/audited increment, including its synchronized README,
results, blueprint and PDF. Do not wait for the entire goal or request routine
publication approval again. The accumulated computational checkpoint is prepared
for publication; the revised scoped theorem is complete and full mechanization of
reduction efficiency remains deferred. The durable full computational
axiom audit is `python3 scripts/audit-helios-computational.py`.

#### Historical goal contract and accumulated checked evidence

The following contract and fragment records preserve the former fully mechanized
efficiency target. Current completion and the external boundary are specified in
C12 above; these records are not instructions to resume the deferred route.

- [ ] **Deferred stronger target.** State the privacy game, corruption policy, challenge admissibility and
  permitted tally disclosure precisely. Establish a Lean-checked reduction
  covering every probabilistic polynomial-time attacker under explicit
  primitive assumptions. Discharge the needed ballot-proof properties,
  disjunctive proofs and Fiat–Shamir context binding for the actual construction;
  account for collisions, tally wraparound, oracle/query and election-size
  bounds, and efficiency. Do not assume the missing correspondence or infer
  security from equal tallies or a blocked attack. Retain the concrete attack
  and honest-ballot controls, audit the public theorem and its axioms, run the
  required builds, and update the results and formal reference with the exact
  completed scope.

  Checked proof prerequisites: `ballotSigma` installs the actual disjunctive
  verifier, commitment/response algorithm and witness extractor in VCVio.
  `ballotTranscript_strongProveVote` identifies its hash-challenged transcript
  with the repaired constructor. `ballotSigma_complete` and
  `ballotSigma_speciallySound` are checked for the nonzero sampler. A full-field
  reference has exact HVZK (`ballotSigma_full_hvzk`); the actual historical
  protocol has `ballotSigma_hvzk` with statistical distance at most `3/|F|`.
  `nonzeroRefill_eq` and `sampleNonzero_uniform_tv_le` derive the sampler bridge.
  The full-field simulator is explicitly not identical to the nonzero prover;
  `nonzero_transcript_ne_full_simulator` retains the separating support witness.
  Equal-challenge and changed-commitment controls reject invalid extraction.
  Integrated and audited: root `lake build`, the Helios claims audit, 73 symbolic
  and 41 computational printed citations, five typed restatements and five gate
  controls pass. All 132 current computational theorem axiom reports are standard
  only. The updated 19-page reference builds without warnings and every final
  page was visually reviewed; its interactive proof section is on page 17.
  Exact controls and log paths are recorded in the results ledger.

  Programming prerequisites now machine-check: `ballotSim_commit_probability_le`
  bounds each simulator commitment by `1/|F|` under generator injectivity;
  `ballotSim_query_collision_le` bounds a fixed prior strong-hash query domain by
  `|Q|/|F|`. `ballotSigma_simChalUniformGivenCommit` establishes the exact VCVio
  companion property on statements with actual bit/nonce witnesses. Checked
  zero-generator and non-bit-statement controls retain both missing-premise
  failures. These distribution prerequisites are integrated and audited: root
  build and Helios audit pass; all 141 computational theorem axiom reports are
  standard only, and the warning-free 20-page PDF was fully visually reviewed.
  The results ledger records the exact controls, citations and log paths.

  The explicit ballot-proof oracle is now implemented: `strongBallotProofOracle`
  retains nonzero sampling and `strongBallotProofOracle_function` proves exact
  agreement with the existing constructor under every typed hash. The verifier
  consumes the original full proof and has the corresponding equality.
  `runBallotOracle_cache_le` and `runBallotOracle_verification_preserved` cover
  arbitrary adaptive oracle computations. `strongBallotSimOracle` programs only
  fresh inputs, preserves prior answers and flags collisions; unflagged outputs
  verify and its flag probability is bounded by a finite initial cache cover.
  Literal fresh/conflicting-cache and changed-statement controls are checked.
  `strongBallot_programming_step_distance_le` now checks the full proof,
  internal flag and final-cache distance `3/|F| + |Q|/|F|`, assuming a valid
  witness, generator injectivity and a finite cover Q of the initial cache.
  It connects the actual nonzero oracle run to the implemented simulator.
  Empty-cache and populated-cache controls check; exact multiplicative
  enumeration covers 24 distributions over q=3,5,11, both bits and four cache
  regimes, with zero failures/gaveUp.

  `runBallotOracle_cache_bound` derives finite cache coverage for supported
  adaptive executions: initial budget k plus at most n hash queries gives k+n.
  Uniform sampling costs zero. `strongBallot_programming_after_queries_le`
  discharges the one-step cover premise after such a run from an empty cache.
  `strongBallot_programming_distance_le` now composes honest-proof requests,
  raw hash queries and uniform sampling under one fixed generator/key. Its
  state-inclusive TV bound is `p * (3+k+n) / |F|` for initial budget k, at most
  p proof requests and at most n hash-or-proof requests. Generator injectivity
  remains explicit; statements are constructed from requested bits/nonces, so
  their witness validity is derived. Proof requests are internal challenger
  operations returning only proofs; the sticky collision flag remains internal.
  `runBallotProofReal_request` identifies requests with the existing historical
  prover/runtime. `runBallotProofSim_flag_sticky` prevents later fresh requests
  from clearing an earlier collision. Kernel controls and 132,860 exhaustive
  adaptive cache traces pass. Root build, full axiom audit and the synchronized
  23-page reference gates/visual review pass. See the results ledger for evidence.

  Selected live-target replay extraction now checks in `BallotFork`.
  `ballotFork_runtime_eq` proves exact agreement with the existing lazy oracle
  after projecting the wrapper cache/log. `ballotFork_selector_reachable`,
  `ballotFork_target_eq` and `ballotFork_selected_challenge` derive the physical
  query and complete statement/commitment agreement from supported contextual
  replays. `ballotFork_extract_valid` gives actual bit/nonce witnesses;
  `ballotFork_extraction_probability_le` bounds success below by
  `a * (a/(n+1) - 1/|F|)`, with a the selected live-target probability and
  truncated subtraction. The private Unit adapter supplies trace machinery;
  no security theorem about its unused relation/methods is used. Controls show
  a real one-query prover has a=1 and positive extraction probability, unrelated
  same-index traces have different keys, and unchecked response normalization
  can erase rejection of a malformed full proof. The independent multiplicative
  harness checks 2,420 extraction pairs and detects 242 normalization defects.
  Integrated: root build and all 204 computational axiom reports pass; the
  warning-free 24-page reference passes citation/statement gates and full
  visual coverage (new extraction section: page 22). See the results ledger.

  Actual verifier acceptance now replaces the selector-only probability in the
  raw ballot-oracle bound. `ballotForkComplete` appends the verifier's existing
  hash query without modifying the returned full proof.
  `ballotFork_complete_runtime` proves exact agreement with the original
  verification game. `ballotFork_log_bound`, `ballotFork_selector_of_bound`
  and `ballotForkComplete_query_bound` derive cache/log coverage and n+1 total
  queries from the original n-query structural bound.
  `ballotFork_acceptance_probability_eq` identifies the complete selector with
  actual acceptance, including previously unqueried targets;
  `ballotFork_acceptance_extraction_le` uses that probability in the same
  replay bound. The 1/|F| term remains. Checked controls retain unqueried
  acceptance 1/11 (the old live-only wrapper gives zero) and exact trace
  preservation for an already queried honest prover. The independent harness
  checks 5,324 verifier-completion cases and detects 242 omitted-query defects.
  Integrated: root build, all 215 computational axiom reports and the 25-page
  reference gates/visual review pass (§14.6, page 23). Logs and limitations
  are recorded in the results ledger.

  Actual repaired-board provenance now checks. `repairedSubmit_acceptance_iff`
  inverts the real decision; `repairedSubmit_accepted_target_ne` excludes all
  component/aggregate cross-kind targets on prior accepted ballots.
  `repairedCastHonestPair_board_of_accepted` derives both honest entries from
  their decisions; `strongHonestBallot_covered_statement` identifies their actual
  nonce/bit statements. `accepted_honest_target_match_implies_rejection` and
  `_implies_collision` show that an accepted generated-honest statement match
  forces rejection/collision. `accepted_honest_target_match_probability_le`
  bounds it by 9/(|F|-1), even for an arbitrary probabilistic hash/ballot
  continuation given the coins. This auxiliary bound does not disclose coins
  in the protocol game. `strongBallotSimOracle_other_statement` and
  `repairedSubmit_accepted_simulation_preserves_target` connect actual weeding
  to preservation of the target cache entry by a local simulation step.
  Controls retain a fresh third accepted ballot, cross-kind rejection, and a
  rejected honest ballot whose complete proof target recurs in an accepted
  submission. The unconditional generated-target-freshness shortcut is false.
  Independent enumeration checks 120,000 weeding/target cases, including
  10,700 accepted recurrences after honest rejection; none violates the
  rejection/collision implication. The negative fixture is reachable under
  the original nonzero sampler and its matching event has positive probability.
  Integrated: root build, all 232 computational axiom reports and the
  warning-free 26-page reference gates/visual review pass (§14.7, page 24).

  The replayable `ballotProgrammedImpl` now lifts the existing simulator,
  forwards fresh raw queries, preserves shadow hits, and records requested
  statements with the sticky flag. `ballotProgrammed_runtime_eq` proves exact
  agreement with the existing adaptive simulator from empty initialization,
  including the original final cache/flag. `ballotProgrammed_request_provenance`
  derives live-answer preservation and cache agreement outside requested
  statements for every supported run. `ballotProgrammed_verify_agreement`
  compares the original full proof under explicit statement exclusion;
  `ballotProgrammed_query_bound` transfers the source request bound to live
  hash queries. The generic composition/projection and lifted-sampler query
  bound reuse pinned VCVio. Controls retain programmed-only hits, conflicts,
  sticky flags and verification disagreement at a programmed target, and refute
  erased provenance/inconsistent initial caches. The independent cache harness
  adds 22,621 dual-cache adaptive trace prefixes with zero failures/gaveUp.
  Integrated and audited: root build, all 245 public computational axiom reports
  and the warning-free 27-page reference pass (§14.8, page 25), with full visual
  coverage recorded in the results ledger. This closes the adapter increment;
  the full computational secrecy milestone remains open.

  `strongHonestBallotOracle` now samples the historical nonce pair and makes
  the three actual proof requests. `strongHonestBallotWithCoinsOracle_function`
  matches the original full constructor for every static hash/coin record;
  `ballotRealRequest_runtime_eq` preserves arbitrary real request runtimes.
  `drawHonestCoinsByProof_eq` proves the necessary independent-coin permutation,
  and `strongHonestBallotOracle_real_eq` connects to the original sampler with
  the final cache and flag. `_request_targets` derives the three returned covered
  statements and preserves prior request metadata from arbitrary initial states.
  `_query_bounds` derives the three-request budget; `_simulation_le` gives
  state-inclusive distance 3*(6+k)/|F| with initial cache budget k and injective
  generator. Zero aggregate nonces remain possible and a checked supported
  fixture validates their honest proof. Controls reject using a component nonce
  for the aggregate and omitting the coin transpose. The independent gate checks
  2,048 coin permutations and 4,096 full-ballot comparisons over labelled
  nonzero draws {1,2}; it detects 4,096 wrong-sum and 3,584 transpose defects.
  Integrated and audited: root build, all 262 public computational axiom reports
  and the warning-free 28-page reference pass (§14.9, page 26), with full visual
  coverage recorded in the results ledger. Board decisions and full secrecy
  remain open.

  Actual full-proof verification and `repairedSubmitOracle` now preserve the
  original algorithms under static interpretation, with invalid-proof rejection
  before expanded reuse and both rejected boards retained. Honest construction
  derives full cached validity, including target collisions; accepting actual
  lazy verification derives cached challenges for all three unchanged proofs.
  Actual acceptance derives freshness and board append. The sampled prefix
  `repairedCastHonestPairOracle_real_eq` matches the historical pair sampler plus
  explicit-coin oracle execution, including decisions, board, cache and flag.
  `repairedCastHonestPairOracle_programmed_targets_of_accepted` derives recorded
  targets' membership in the returned board when both honest decisions accept.
  `repairedHonestPrefix_accepted_target_exclusion` excludes those targets after
  arbitrary raw attacker queries and an actual accepted submission. Raw queries
  preserve request metadata; no caller freshness/presentation premise is added.
  Controls retain all three decisions, aggregate-only failure, proof-rejection
  priority and actual static-prefix acceptance/rejection. Their preloaded-cache
  fixture does not claim empty-cache reachability. Independent full-proof checks
  cover 16 validity/freshness cases and detect seven priority defects and two
  aggregate-check omissions; zero failures/gaveUp. The rejected-target recurrence
  counterexample remains checked. Integrated and audited: root build, all 286
  computational axiom reports, independent gate and the warning-free 29-page
  reference pass (§14.10, page 27). Visual coverage and logs are recorded in the
  results ledger. This closes the accepted-prefix increment, not full secrecy.

  `HonestPrefixRejection` now derives actual real-prefix rejection ≤9/(q−1)
  from returned nonce coordinates, cached validity and the historical collision
  bound, with generator injectivity and arbitrary initial cache. The actual
  source budget is twelve hash-or-proof requests, including six honest proofs;
  `repairedCastHonestPairOracle_simulation_le` gives state-inclusive TV ≤6*(15+k)/q.
  The simulated rejection bound retains both losses; exact adapter runtime gives
  `repairedCastHonestPairOracle_programmed_rejection_le` at 9/(q−1)+90/q from
  empty initialization. At q=101, checked programmed acceptance has positive
  probability; a zero-generator control refutes dropping injectivity. Original
  rejection and zero-aggregate controls remain. Independent full-oracle prefix
  fixtures check 40,000 cases, including 11,200 retained rejections and 7,600
  zero-aggregate prefixes, with no failures/gaveUp. Integrated and audited: root
  build, all 299 computational axiom reports and the warning-free 30-page
  reference pass (§14.11, page 28); full visual coverage is recorded in the
  results ledger. Computational secrecy remains open.

  Selected-proof composition now checks. `repairedSubmissionOracle` runs the
  actual programmed prefix, a raw attacker given its decisions/board, and
  original submission. `_accepted_live` derives full live verification from
  actual intermediate-state provenance and accepted-target exclusion. The replay
  target retains the original full proof on joint acceptance and uses an always
  invalid proof otherwise; actual verifier acceptance is exactly joint acceptance.
  The source/lowered budget is n+15 for attacker hash budget n. With B the actual
  attacker-submission acceptance probability, δ=9/(q−1)+90/q, and a=(B−δ) truncated
  at zero, `repairedSubmission_extract_le` bounds extraction below by
  a*(a/(n+16)−1/q), again using truncated subtraction. `_extract_origin` ties each
  returned valid bit/nonce witness to the selected ciphertext of a supported
  accepting submission. It is existential source origin, not joint extraction
  for a fixed original ballot. Controls retain unchanged accepted proofs, a
  rejected honest prefix followed by an accepted valid ballot, the invalid guard
  and its retained hash query. Independent programmed-prefix/attacker fixtures
  check 20,000 cases, with 2,720 joint acceptances and 2,840 excluded valid
  submissions after prefix rejection; zero failures/gaveUp. Integrated root build,
  all 320 computational axiom reports and the warning-free 31-page reference pass
  (§14.12, page 29). The results ledger records full visual coverage and audit
  logs. Computational secrecy remains open.

  First-source retention now checks. `ballotForkSource_trace_eq` expresses the
  old trace as an exact projection of original source execution plus the existing
  completion query. VCVio's `contextForkWitness` already retains both typed paths;
  PolyFun's `Path.pullMap` recovers the first source leaf. This avoids the planned
  new trace format. `repairedSubmission_extractSource_valid` proves that the
  returned complete submission accepted and its chosen ciphertext has the
  extracted witness. `_project` gives exact old-extractor equality after dropping
  the source; `_probability_eq`/`_le` retain the preceding bound without extra loss.
  Controls prove positive extraction and that the retained tag follows the first
  proof. Valid same-target replay transcripts can change that tag. The independent
  multiplicative gate checks 2,420 replay pairs, detecting 440 wrong-second-tag
  cases; prior full-proof and completion controls remain. Integrated root build,
  all 338 computational axiom reports and the warning-free 32-page reference pass
  (§14.13, page 30). The results ledger records full visual coverage and audit
  logs. Joint extraction and computational secrecy remain open.

  Joint-witness algebraic contract now checks in `BallotWitnessConsistency`.
  `Ballot.covered_witnesses_sum` derives aggregate nonce/scalar-message sums from
  three actual ciphertext witnesses. `_atMostOne` derives the integer count with
  (2:F)≠0; `_atMostOne_prime` discharges it for prime ZMod q with q>2. This consumes
  witnesses, without assuming that accepted proofs already yield them. Controls
  retain honest/abstention witnesses and a four-element characteristic-two model
  where both component bits one have aggregate bit zero and original full proofs
  validate; original empty-board submission accepts. This refutes a cardinality
  >2 shortcut, not the historical large prime-order protocol. The independent
  gate checks 10,648 multiplicative witness comparisons, 363 consistent triples,
  121 omitted-aggregate double-vote cases and 16 characteristic-two wraps.
  Integrated root build, all 346 computational axiom reports and the warning-free
  33-page reference pass (§14.14, page 31). The results ledger records full visual
  coverage and logs. Joint replay and computational secrecy remain open.

  Joint replay construction now checks. `ballotReplayAtPath_bind` factors the
  existing rich fork into one original path and a conditional completion.
  `ballotReplaySourcePath_output`/`_queries` preserve the original output and
  every query answer; `_distribution` and `ballotReplaySourceAttempt_bind`
  exactly recover the raw selected-proof extractor marginal. The actual
  `repairedSubmission_joint_extract_valid` derives all three ciphertext witnesses
  for its one returned original accepting submission, and `_consistent` derives
  nonce sums and integer at-most-one with (2:F)≠0. No caller supplies witnesses
  or source agreement. The repeated-target positive control and original-tag
  theorem check; disjoint marginal success sets refute inferring joint success
  from separate first paths. Independent multiplicative fixtures enumerate 31,944
  three-proof replay cases (3,993 joint successes, 27,951 retained failures) and
  detect 8,712 wrong-second-source substitutions. This finite campaign is not
  an arbitrary-attacker probability bound. Integrated root build and all 363
  public computational axiom reports pass with standard axioms only. The
  warning-free 34-page reference passes its citation and typed-interface audits;
  §14.15 is page 32. All changed pages were visually inspected, with unchanged
  page hashes reusing the prior review. Logs are in the results ledger.

  Accepted-path query coverage now checks in `RepairedSubmissionCoverage`.
  `ballotReplaySourcePath_runtime_mem` retains the exact original live cache.
  `repairedSubmissionPath_verified` and `_selector` identify the full-proof
  verification flag and bounded selector with joint acceptance on every original
  path. `_locations` derives all three physical replay occurrences; no caller
  supplies live validity, cache/log correspondence or a completion query.
  `_selection_probability` proves that simultaneous original selection has
  exactly the actual joint acceptance probability. Independent multiplicative
  fixtures check 60,000 selector cases over 20,000 original source fixtures,
  with 8,160 enabled selections and 8,160 detected omitted-miss-target defects.
  Existing invalid-fallback, unqueried-verifier and replay controls remain.
  Normal module export and root build pass; all 368 public computational axiom
  reports are standard-only. The reference audits and warning-free 34-page PDF
  pass (§14.15, page 32), with final visual coverage recorded in the results
  ledger. Fresh module export took 220 seconds; incremental checks reuse it.

  The quantitative common-path bound now checks. `ballotJointReplay_bad_context_le`
  bounds low-mass contexts by 3Qδ, and `repairedSubmission_joint_extract_le`
  proves success ≥ (a−3Qδ)₊(δ−1/q)₊³ for Q=n+16 and
  a=(B−9/(q−1)−90/q)₊, where B is actual accepted-submission probability.
  The stronger bound uses actual joint acceptance. Physical-context reconstruction,
  uniform focused challenges and the three actual conditional binds discharge the
  argument without multiplying unrelated marginals. δ is an analysis parameter.
  A missing-occurrence counterexample retains the reachability requirement; the
  honest tagged control gives the positive bound 27/2725888. Independent exact
  branching-tree fixtures validate the context and collision calculations.
  Root build and all 385 public computational axiom reports pass with standard
  axioms only. The audited, warning-free 35-page reference passes; §14.16 is page
  33. Changed pages were visually inspected; unchanged hashes reuse prior review.
  Integrated evidence is recorded in the results ledger.

  Oracle-interaction accounting now checks in `BallotReplayCost`:
  `ballotReplaySourceRun_total_query_bound` derives the logging bound from the
  raw source; `ballotReplay_occurrence_total_bound` bounds every physical
  completion. `ballotJointReplay_total_query_bound` gives 4m total interactions
  from a raw-source bound m, including uniform draws and all three attempts.
  The honest tagged extractor instantiates m=1. Controls refute omitting the
  original run or treating uniform draws as free, and show that query cost
  assigns zero to arbitrary pure functions. It is not a PPT certificate.
  Independent reachable-tree fixtures pass 8,691 cases with 93 exact equalities
  and detect both accounting defects. Root build and all 394 public computational
  axiom reports pass with standard axioms only. The audited 35-page PDF is
  warning-free; its changed page 33 is visually reviewed and other hashes match
  the prior reference. Integrated logs are in the results ledger.

  Actual repaired-source accounting now checks in `RepairedSubmissionCost`.
  `repairedSubmissionOracle_total_query_bound` derives m+19 before lowering:
  four nonzero nonce draws, six proof requests, at most nine verification queries
  and at most m attacker interactions per view. Each lowered handler costs at
  most four, giving `repairedSubmissionSource_total_query_bound` at 4(m+19) and
  `repairedSubmission_joint_extract_total_query_bound` at 16(m+19). These are
  conservative interaction bounds, separate from the secrecy loss and hash-budget n.
  The scalar sampler's one-query cost is explicit; `canonicalSampler_total_query_bound`
  and `repairedSubmission_joint_extract_canonical_total_bound` discharge it for
  `SampleableType.ofFintype`. A checked padded uniform sampler refutes inferring
  cost from distribution. A simulated proof cannot be charged as one draw; the
  actual constant-attacker extractor instantiates the general bound at m=0.
  Independent finite accounting checks 1,755 cases and detects omitted nonces,
  undercharged proof requests and discarded sampler draws. Root build and all
  402 public computational axiom reports pass with standard axioms only. The
  audited reference is warning-free and remains 35 pages; changed page 33 is
  visually reviewed and other hashes match the prior reference. Integrated
  evidence is recorded in the results ledger.

  Finite live-cache implementation now checks using Mathlib `AList`, with no
  new map framework or dependency. `runBallotFiniteCache_eq` preserves every raw
  program's output, explicit random draws and final semantic cache exactly;
  `_length_le` derives storage growth from the existing query-bound theorem.
  `repairedSubmissionFiniteCache_eq` and `_length_le` instantiate the actual
  source and prove at most n+15 stored entries. The semantic cache, source and
  probability proofs remain intact; no caller supplies state correspondence.
  Controls cover hits, misses, repeats, prior state and complete-key separation.
  Independent reachable histories check 11,656 cases, with 6,656 hits and 5,000
  misses, and detect overwrite/drop-state/drop-statement mutations. Root build
  and all 414 public computational axiom reports pass with standard axioms only.
  The audited, warning-free 36-page reference passes; §14.17 is page 34. Changed
  pages were visually reviewed and unchanged hashes match the previous reference.
  Integrated evidence is recorded in the results ledger.

  The programmed shadow cache now uses the same AList carrier.
  `runBallotFiniteProgrammed_eq` checks arbitrary initial finite states and full
  programs; `_runtime` composes both finite caches, preserving output, sticky
  flag and exact requested-statement list. `repairedSubmissionFiniteSource_eq`
  gives exact raw-source equality, allowing existing replay results to use the
  finite representation; `_length_le` retains n+15 live entries. The root build,
  all 425 public computational axiom reports and formal-reference audits pass.
  The warning-free PDF has 37 pages; §14.18 is page 35. All changed pages were
  visually reviewed, with unchanged pages matching prior reviewed hashes.
  Independent reachable state histories check 69,904 transitions and detect
  overwrite, reset-flag and deduplicated-history defects. Collision controls
  retain occupied agreeing answers and fresh requests after earlier failure.

  Saved replay input now uses PolyFun's existing finite tagged event list.
  `ballotReplayReadTape_trace` and `_exact` reconstruct the exact path and reject
  unconsumed input; `ballotReplayCollectTape_eq` preserves the actual random
  computation. `ballotJointReplayTape_eq` and `repairedSubmissionTape_extract_eq`
  preserve the three attempts, original source result and all failure behavior.
  The actual saved tape has at most 4(m+19) entries with one-query scalar sampling;
  canonical sampling retains the 16(m+19) interaction bound. Literal controls
  retain branch-dependent tags, truncation, trailing data, ordering, uniform
  answers and the second repeated hash occurrence. Independent finite checks
  cover 6,705 valid paths and 20,025 malformed tapes. Root build and all 440
  public computational axiom reports pass with standard axioms only. The
  warning-free PDF has 38 pages; §14.19 is page 36. Changed pages were visually
  reviewed and unchanged hashes match the prior reference. Integrated evidence
  is recorded in the results ledger.

  Finite replay logging now checks using the existing AList cache and exact
  chronological miss-log format. `runBallotFiniteLogged_eq` covers arbitrary
  finite initial caches/logs; `ballotFiniteReplaySourceRun_eq` identifies the
  lowered source. `ballotFiniteJointReplay_eq` uses this finite interpreter in
  the original execution and all three residual attempts, preserving the actual
  joint algorithm. `repairedSubmissionFinite_extract_eq` instantiates the finite
  shadow source; original miss-log length is at most n+15 and canonical total
  interactions remain 16(m+19). Controls preserve hits, uniform forwarding,
  full-key separation, log order and multiplicity. Independent state histories
  check 11,110 transitions and detect duplicate-hit, prepend-order and
  commitment-only mutations. The root build and all 456 public computational
  axiom reports pass with standard axioms only. The warning-free PDF has 39 pages;
  §14.20 is page 37. All changed pages were visually reviewed and unchanged hashes
  match the previous reference. Integrated evidence is recorded in the results ledger.

  Finite replay storage now derives the initial cache/log size offset for every
  supported execution. Empty initialization gives equal sizes and at most n+15
  cache entries and log entries in the actual source. The exact eight-field key
  layout is injective, decodes back exactly and rejects other lengths; the
  cache/log records contain at most 16(n+15) group elements and n+15 scalar
  answers. Controls retain the preloaded-cache counterexample and literal field
  order. Independent enumeration checks 18,720 transitions from four initial
  cache/log states and detects two broken updates. This counts replay cache/log
  element cells, not bit lengths, all retained state or execution time.
  Integrated root build and all 473 computational theorem axiom reports pass
  with standard axioms only. The warning-free 40-page PDF includes §14.21 on
  page 38; all changed pages were reviewed. Full evidence is in the results
  ledger. These are storage results; the computational secrecy milestone remains
  open.

  Shadow storage now derives additive cache and proof-history growth bounded
  by the source total-query budget, from arbitrary initial states.
  `repairedSubmissionFinite_shadow_runtime_storage_le` instantiates the actual
  probabilistic finite-live execution: m+19 entries in each shadow structure
  from the attacker's per-view total bound m, without a sampler-cost assumption.
  The repeated-programming control has one cache entry and two history entries;
  fresh programming after that gives two and three. The independent harness
  retains the original 69,904 transition comparisons and adds 17,472 size-offset
  transitions from four initial states. Its comparator now checks entry count:
  dictionary projection alone hid the new duplicate-insertion mutant.
  Integrated root build and all 478 computational axiom reports pass with
  standard axioms only. The warning-free 41-page PDF includes §14.22 on page 39;
  all changed pages were reviewed. Integrated evidence is in the results ledger.

  Actual output bounds now derive at most two honest-prefix board entries
  and three final-board entries for every supported source/runtime output,
  retaining rejection behavior. Ballot record projections expose every stored
  ciphertext, commitment, challenge and response: 16 group/12 scalar fields
  per ballot, and at most 96/72 in all retained output ballots. Decisions and
  identifiers remain in the output. Literal field-order controls and the
  independent 27-history retention fixture distinguish omitted fields and
  incorrect append/drop behavior; previous cryptographic board controls remain.
  `BallotTapeOperandControls.wide_tape` checks a supported one-query tape whose
  range tag 2^k has k+1 binary bits. `.no_count_only_tag_bound` refutes every bound
  depending only on event count; the zero answer and small coin fixture exclude
  attributing this to long tapes or answer size. Independent width fixtures
  cover 514 power/boundary cases. Root build and all 489 computational axiom
  reports pass with standard axioms only. The warning-free 42-page PDF has
  §14.23 on page 40; all changed pages were reviewed. Integrated evidence is
  recorded in the results ledger. Full computational secrecy remains open.

  The narrow encoding comparison confirms that pinned VCVioComplexity offers
  unary naturals and fixed-width BitVec, but lacks binary naturals and general
  oracle-machine adequacy. No dependency or upstream revision was changed.
  `UniformOperandCodec` now uses Mathlib binary digits with an explicit width
  prefix for actual uniform range/answer events. Prefix round trips preserve
  arbitrary suffixes; successful decoding reconstructs the exact input. Event
  decoding checks answer range and complete consumption. Encoded event length
  is 2*size(n)+2*size(a)+2; the supported wide-tag family has 2k+4 bits. Controls
  detect padding, truncation, range and trailing-data errors. The independent
  gate checks 2,145 valid events and all 8,191 words up to length 12 after
  detecting three mutated decoders. Root build and all 499 computational axiom
  reports pass with standard axioms only. The warning-free 43-page PDF has
  §14.24 on page 41; all changed pages were reviewed. Integrated evidence is in
  the results ledger. This is an operand codec, not a machine
  implementation, operation-cost certificate or full secrecy proof.

  `ScalarCodec` now encodes historical ZMod q residues canonically, rejecting
  values at or above q and deriving a modulus-width length bound. The complete
  actual entropy tape contains uniform events and scalar challenges, with no
  group keys. `ReplayBitsCodec` proves exact decoding, count/length framing and
  complete consumption. `repairedSubmissionBits_extract_eq` identifies the direct encoded-frame
  collector and replay from saved bits with the existing repaired joint
  extractor, including all three attempts and failure paths. Literal controls
  and the independent gate cover 4,760 tapes, 14,278 malformed variants and
  32,767 arbitrary words; three decoder mutants are detected first.
  Root build and all 519 public computational axiom reports pass with standard
  axioms only. The warning-free 44-page reference has §14.25 on page 42; all
  changed pages were reviewed. Integrated evidence is in the results ledger. This closes internal entropy encoding,
  with OracleComp continuation costs still open.

  Pinned VCVio already supplies computable ZMod enumeration via FinEnum and
  Mathlib's Fin equivalence. `primeScalarSampler_total_bound` reuses it;
  `repairedSubmission_joint_extract_prime_total_bound` applies it to the actual
  extractor without the noncomputable ofFintype substitution. `samplePrimeNonzero`
  samples Fin(q−1) and returns i+1. `samplePrimeNonzero_bind` and
  `drawPrimeNoncePair_bind` preserve every ProbComp continuation distribution,
  including independence. The historical generic nonce definition is retained
  as the baseline; the source integration below leaves replay replacement open.
  Independent fixtures cover 38 residues and 412 ordered pairs over five small
  primes, detecting zero-offset, omitted-endpoint, repeated-draw and modulo-bias
  mutants first. Lean controls distinguish pair probability 1/16 from zero under
  nonce reuse at q=5. Root build and all 529 public computational axiom reports
  pass with standard axioms only. The warning-free 45-page PDF has §14.26 on
  page 43, with every changed page reviewed. Integrated evidence is in the
  results ledger; full computational secrecy remains open.

  `repairedSubmissionWithNoncePairs_original` now recovers the original source
  exactly after factoring its two nonce-pair draws. `repairedSubmissionPrimeOracle`
  uses the explicit sampler at both positions. `repairedSubmissionPrime_runtime_bind`
  preserves the complete finite runtime under arbitrary initial states and
  subsequent ProbComp continuations; `_runtime` specializes to the real empty
  initial state. Both finite caches, sticky flag, ordered request history and all
  decisions/boards are retained. `repairedSubmissionPrimeSourceOracle` is the
  computable lowered raw source; `_runtime` preserves its result/live-cache law.
  Actual nonce-state controls retain a prior collision and duplicate history;
  independent synthetic continuation fixtures cover 23,136 tuples and detect
  correlated pairs, reset state and dropped rejection branches first. Root build
  and all 536 public computational axiom reports pass with standard axioms only.
  The warning-free 46-page PDF has §14.27 on page 44; all changed pages were
  reviewed. Integrated evidence is in the results ledger. This closes submission-source replacement,
  with the replay closure recorded next.

  Explicit-source replay is now proved by reapplying the existing generic
  theorem to that source, without an old/new path correspondence. The actual
  syntax derives n+15 hash requests; supported result/cache transport supplies
  cached validity, and selectors/physical locations are derived on the new
  source's own paths. `repairedSubmissionPrimeBits_extract_valid` and `_consistent`
  return all three witnesses for the original accepted ballot, with the prime
  q>2 integer vote constraint. `_le` preserves the historical joint success bound
  and honest-rejection/simulation loss. `_total_bound` derives 16(m+19) from
  per-view attacker total bound m, using the computable scalar/nonce samplers.
  No selector, witness, sampler-cost or replay-correspondence premise remains.
  Existing nonce/state/rejection controls and independent context/tape gates
  pass. Root build and all 557 public computational axiom reports pass with
  standard axioms only. The warning-free 47-page PDF has §14.28 on page 45,
  with all changed pages reviewed. Integrated evidence is in the results ledger.

  `coinProgram_has_bound` and `coinProgram_dyadic` now derive a finite maximum
  coin count and dyadic probabilities for every actual terminating coin program.
  `coinProgram_not_prime_uniform` therefore excludes exact odd-prime uniform
  sampling in that representation, without a caller-supplied budget. The checked
  two/four-outcome positives and modulo-three bias retain the representation
  boundary. Classify this as a representation obstruction, not a protocol bug.
  The independent finite gate detects both uniform-modulo and zero-cutoff-failure
  mutations; it has no failures or gaveUp outcomes. Root build and all 564
  public computational axiom reports pass with standard axioms only. The
  warning-free 48-page PDF has §14.29 on page 46; all changed pages were visually
  reviewed. Integrated evidence is recorded in the results ledger.

  The selected sampler is now implemented. `sampleFairBitIndex_probability`
  reuses VCVio's independent-product law and Mathlib's computable binary-digit
  equivalence. `sampleFairBitModulo_probability` gives the exact residue mass;
  `_tv_le` bounds its distance by the incomplete-block mass. With q.size+s bits,
  `sampleFairBitRange_tv_le` gives error ≤2^(-s), including arbitrary common
  probabilistic continuations; `_query_bound` counts actual bit requests.
  `runFairBitUniform_tv_le` composes the error over adaptive source queries,
  and `_support_subset` independently derives reachable-output preservation.
  The existing exact entropy interpreter lowers both index and scalar queries
  in the actual joint extractor, with a derived one-query cost for each.
  `repairedSubmissionFairBits_extract` now uses only fair-bit queries.
  Its `_valid`/`_consistent` preserve the three witnesses and integer constraint;
  `_le` retains the historical success bound minus the explicit sampling term
  ofReal(16(m+19)*2^(-s)). No correspondence or primitive-cost premise is added.
  Literal and adaptive controls retain residual modulo bias, digit order and
  response-dependent ranges. Independent rational fixtures detect four mutants
  and pass all finite masses, events and width checks. Root build and all 586
  public computational axiom reports pass with standard axioms only. The
  warning-free 50-page PDF has §§14.30–14.31 on pages 47–48; every changed page
  was visually reviewed. Integrated evidence is recorded in the results ledger.

- [x] Supply the concrete public-coordinate prime subgroup and canonical group
  codec needed by encoded hash keys, caches and boards. Reuse Mathlib's roots
  of unity and ZMod module; preserve identity and the actual ElGamal equations.

  `primeGroupCoordinate_smul` and `primeGroup_encrypt_coordinates` connect the
  existing algorithms to modular exponentiation. For prime q and a nonidentity
  generator, `primeGroup_generator_injective` derives the extraction premise;
  prime p additionally gives cardinality q in `primeGroup_card`.
  `primeGroupDecode_encode`, `_exact` and `primeGroupEncode_length_le` give
  round trip, canonical acceptance and the public-modulus width bound.
  Literal controls cover p=23/q=11, ciphertext (16,4), identity, nonmembership,
  aliases and trailing bits. Independent integer fixtures cover small prime
  groups and detect missing membership, modulo-alias and excluded-identity
  mutations. Integrated root build and all 606 public computational axiom reports
  pass with standard axioms only. The warning-free 51-page PDF has §14.32 on
  page 49; every changed page was visually reviewed. Full evidence is recorded
  in the results ledger.
  This supplies a primitive internal representation, not an assembled cache or
  board codec, raw election parser, operation-cost certificate or PPT theorem.

- [x] Assemble complete full-key and ordered finite-cache bit records, with
  exact decoding, concrete lookup/insertion correspondence and a reachable
  source-derived bit-length bound.

  `ballotKeyBits_roundTrip`/`_exact` retain all eight group fields.
  `ballotCacheBits_roundTrip`/`_exact` and `_injective` retain every answer and
  entry order; `_duplicate` rejects duplicate full keys, even agreeing answers.
  `ballotCacheBitsLookup_encode` distinguishes a valid miss from malformed
  records; `ballotCacheBitsInsert_encode` agrees with actual AList insertion.
  `ballotCacheBits_length_le` accounts for every framing bit, key and answer.
  `repairedSubmissionPrime_cache_bits_le` derives the bound from the explicit
  source's own n+15 budget; the older finite source is covered separately.
  The common list/pair framing is shared by cache fields and later boards;
  it assumes no protocol correspondence or machine-cost certificate. Public
  coordinate comparison supplies executable group equality. Independent fixtures
  detect key-field omission, duplicate acceptance and ignored trailing input;
  kernel controls also distinguish reordered entries with the same lookup map.
  Integrated root build and all 631 public computational axiom reports pass
  with standard axioms only. The warning-free 52-page reference has §14.33 on
  page 50; every changed page was visually reviewed. Reproduction evidence is
  recorded in the results ledger.
  This closes standalone keys/caches, not complete logged/programmed states or
  boards. Record lengths and encoded operation agreement do not prove PPT costs.

- [x] Assemble the complete finite logged/programmed interpreter data, preserving
  both caches, the collision flag, ordered miss log and repeated request history.
  Derive full record bounds from the actual explicit source's own budgets.

  `ballotLoggedBits_roundTrip`/`_exact`, `ballotProgrammedBits_roundTrip`/`_exact`
  and `ballotBothCachesBits_roundTrip`/`_exact` check canonical whole-data
  records. The unique Unit log tag uses an explicit equivalence; no history
  deduplication or reversal occurs. `ballotProgrammedBitsApply_encode` preserves
  the actual transition and returned typed proof. `repairedSubmissionPrime_logged_bits_le`
  derives n+15 for log/cache; `repairedSubmissionPrime_bothCaches_bits_le`
  derives m+19 for shadow/history and n+15 for the live cache, from actual
  runtime support. No cache cover, replay correspondence or cost premise is added.
  Controls retain the old answer on collision, set the flag and prepend repeated
  requests; they distinguish erased flags/live caches and reversed miss logs.
  Independent integer fixtures exercise both initial flags, every scalar
  challenge, fresh/occupied keys and complete record bounds, detecting five
  state mutations. Integrated root build and all 651 public computational axiom
  reports pass with standard axioms only. The warning-free 53-page reference
  has §14.34 on page 51; every changed page was visually reviewed. Reproduction
  evidence is recorded in the results ledger.
  These are complete finite interpreter data records. OracleComp continuations
  and proof/ballot/board/submission-output records remain separate; machine
  execution costs and adequacy are still open.

- [x] Encode complete proof/ballot/board/submission data and every existing
  public election-view field. Connect encoded submission/finishing interfaces
  and the actual internal runtime bit result to their original computations.

  `ballotBits_roundTrip`/`_exact`, board/submission variants and the public
  prefix/result variants preserve the complete objects. Voter IDs, both honest
  decisions, rejection reasons, trustee proofs, candidate/voter lists,
  fingerprint, encrypted tally, shares and Option Nat decoded tallies remain
  explicit. The codec admits well-typed invalid ballots; the original verifier
  still rejects them. `repairedSubmitBitsOracle_encode` preserves the actual
  shared-oracle program; `finishRepairedElectionBits_encode` preserves the
  complete original typed-hash finishing output. Neither defines raw-input policy.
  `repairedSubmissionPrime_output_bits_le` derives the submission-size bound
  from actual runtime board counts. `repairedSubmissionRuntimeBits_decode` and
  `_length_le` provide an actual internal bit-result program, exact full-data
  decoding and combined submission/state bound with own hash/total budgets.
  Private interpreter data is not added to public observations. Pair/list size
  helpers are reused from the prior state proof, without new assumptions.
  Independent fixtures distinguish twelve public-field mutations, None/zero,
  all decisions and board order, and check 36 submission-size cases. Kernel
  controls retain invalid-proof rejection and mutated aggregate/metadata fields.
  Integrated root build and all 684 public computational axiom reports pass
  with standard axioms only. The warning-free 54-page reference has §14.35 on
  page 52; all changed pages were visually reviewed. The results ledger records
  reproduction evidence. Computational milestones remain 2/3 complete; Step 3 active.
  Full-public-view Nat/list metadata keeps its actual widths; no fixed bound
  for an arbitrary fingerprint function is assumed. Full shared-oracle election
  integration, raw-input policy, costs, adequacy and secrecy remain open.

- [x] Implement the loaded-bit comparison needed for complete-key lookup in
  Mathlib's concrete TM2 machine model, with finite control and a derived bound.

  `BitCompareMachine.run` proves terminal control and exact equality on arbitrary
  words within first-word length plus one transitions, for every initial memory.
  `key_run` derives a K(p)+1 fuel bound for original typed-key equality from
  the actual canonical full-key encoder. Two binary stacks, one label and nine
  memory states prevent an unbounded equality callback. Independent exhaustive
  fixtures cover 16,129 word pairs and detect strict-prefix acceptance; Lean
  controls check equality, late mismatch, both prefix orders and continued work.
  Integrated root build and all 692 public computational axiom reports pass
  with standard axioms only. The warning-free 55-page reference has §14.36 on
  page 53; all changed pages were visually reviewed. This closes
  loaded-word comparison only: the current cache wrapper still calls the typed
  lookup after decoding. The next item supplies copying; initial loading, parser
  and enclosing cache scan/update execution remain open. No TM0 cost or complete
  PPT certificate is claimed.

- [x] Implement concrete two-pass copying for loaded query/cache words, retaining
  the source, destination suffix and bit order, and clearing scratch.

  `BitCopyMachine.run` reaches the exact complete halted configuration within
  2*word.length+2 TM2 transitions. Only three binary stacks, two labels and
  optional-bit memory are used. `key_copy` derives ≤2*K(p)+2;
  `source_cache_copy` derives ≤2*B(p,q,n+15)+2 from the actual explicit source's
  supported cache and per-view hash bound. No caller-supplied cache-size or cost
  certificate is added. Independent complete-stack fixtures cover 16,129 cases
  and detect reversed-copy/source-erasure implementations. Lean controls retain
  suffixes, empty words and the incomplete first pass. Integrated root build
  and all 700 public computational axiom reports pass with standard axioms only.
  The warning-free reference remains 55 pages; §14.36 on page 53 now covers both
  comparison and copying and was visually reviewed. Initial encoding/loading,
  parser execution and the lookup/update scan remain open.

- [x] Implement the existing binary-natural prefix parser in the concrete machine,
  with all-raw-input correspondence, rejection and a derived transition bound.

  `NatPrefixMachine.total_run` halts on every word with fuel ≤3*word.length+3
  and exactly matches `uniformNatRead`, outputting literal bits and untouched
  suffix. `encoded_run` uses 3*n.size+3 and clears count/scratch. General rejection
  theorems cover missing delimiters, truncation and high-zero padding; canonicality
  follows from the original codec's laws, with its source unchanged.
  `cache_header_run` extracts the concrete encoded cache's outer count field;
  `source_cache_header` derives ≤3*(n+15).size+3 for supported actual-source caches.
  No well-formedness, cache-size or parser/cost certificate is assumed. Four binary
  stacks, three labels and optional-bit local memory exclude whole-word callbacks.
  Independent exhaustive fixtures cover 8,191 raw words and detect canonicality
  and truncation mutants; Lean controls retain zero, suffix, ordering and rejection.
  Integrated root build and all 719 public computational axiom reports pass
  with standard axioms only. The warning-free 56-page reference has §14.37 on
  page 54; every changed page was visually reviewed. This closes natural prefixes
  and the cache count header, not multi-field record parsing
  or the lookup/update scan. Binary digits have not been converted to an uncharged
  machine Nat. Full historical raw-input policy and computational secrecy remain open.

- [x] Implement canonical binary decrement on the parser's bit-stack layout,
  with exact arithmetic, underflow behavior, preserved frames and bounded execution.

  `BitCounterMachine.run` derives fuel ≤2*n.size+1 for canonical (n-1).bits,
  a nonzero-input flag, empty scratch and unchanged input/count stacks.
  `borrow_chain_run` executes k borrowed zero bits with 2*k+2 fuel.
  `parsed_run` derives the canonical input from the actual successful prefix
  parse and preserves all stack data. This data-interface theorem does not
  provide a combined time bound; the linked field reader below supplies execution.
  Independent fixtures cover 4,341 naturals and borrow chains through 256 bits,
  detecting high-zero retention and lost-borrow mutants. Lean controls retain
  8→7, 1→0, 3→2, zero underflow, flags and unrelated stacks. Targeted and root
  builds pass; all 730 public computational axiom reports use standard axioms only.
  The warning-free 57-page reference has §14.38 on page 55; every changed page
  was visually reviewed. This closes the decrement primitive, not multi-field
  parsing or the all-PPT milestone.

- [x] Execute length-prefixed field reading in one linked TM2 program, including
  all-raw-word rejection and a polynomial bound in raw input length.

  `TM2ReturnLink.run` redirects labels and halt to caller control on unchanged
  stacks/memory, deriving a run no longer than the original even if its fuel
  includes halted padding. `FieldReadMachine.counter_run` uses it inside the
  consuming loop. `run` returns the exact field/suffix and cleared workspace;
  `truncated_run` rejects after at most |input|*(2*n.size+2)+1 transitions,
  retaining the remaining binary count. `FieldPrefixMachine.total_run` links
  the original prefix parser, field reader and final halt, proving every raw
  word w agrees with the single-field decoder within
  3*|w|+5+(|w|+1)*(2*|w|+4) transitions. `singleton_record_run` obtains framing
  from acceptance by the existing record codec, after its outer count header.
  Independent fixtures cover 6,867 count/input cases, widths through 257 bits,
  and 8,191 raw words; reversed-output and truncation-acceptance mutants bite.
  Lean controls retain suffix/order, zero fields, huge-count empty-input
  rejection and malformed headers. Targeted and root builds pass; all 752 public
  computational axiom reports use standard axioms only. The warning-free 58-page
  reference has §14.39 on page 56; every changed page was visually reviewed.
  This closes linked single-field execution. It does not execute a multi-field
  record, its outer count loop, or a cache scan.

- [x] Preserve outer record state across actual field parsing and count decrement.

  `TM2StackFrame` proves exact statement/step/run relocation with an explicit
  extra-stack frame and unchanged fuel. Six binary stacks avoid encoding and
  repeatedly saving/restoring outer state inside the reader's four work stacks.
  `RecordFieldStepMachine.field_run` instantiates preservation for all raw fields;
  `counter_run` relocates decrement onto the outer counter while preserving the
  field and archive. `run` executes one successful iteration in shared control:
  E(|bs|)++bs++suffix, outer (n+1).bits and arbitrary archive become bs, suffix,
  outer n.bits, empty workspace and unchanged archive, with derived fuel
  ≤3*|bs|.size+10+|bs|*(2*|bs|.size+3)+2*(n+1).size. `field_complete` derives the
  complete successful workspace instead of assuming it from readout equality.
  `rejected_run` halts on every rejected raw field before decrement, preserving
  outer count and archive. Independent fixtures cover 10,220 raw-field/frame
  combinations, 257-bit counters and two detected alias mutants. Lean controls
  retain a full 33-step iteration, rejection frames, zero-counter underflow and
  distinct field/count data. Targeted and root builds pass; all 766 public
  computational axiom reports use standard axioms only. The warning-free 59-page
  reference has §14.40 on page 57; every changed page was visually reviewed.

- [x] Archive each consumed original field frame and clear output for reuse.

  `TM2InputArchive.run` proves complete work/control agreement at identical TM2
  fuel, with input=consumed++residual and archive=reverse(consumed)++oldArchive.
  Its structural restrictions are discharged for the actual iteration by
  `ArchivedFieldMachine.eligible`. The checked archive-read counterexample
  retains why that restriction is necessary. `recorded_run` appends exactly
  E(|field|)++field in reverse, retaining original boundary information without
  a second codec. `ArchivedFieldMachine.run` links cleanup and clears count/scratch/output, with outer n+1→n and bound
  ≤3*|field|.size+12+|field|*(2*|field|.size+4)+2*(n+1).size. `rejected_run`
  preserves rejection/count and records only the consumed prefix; failed pops
  cannot add phantom bits. Independent fixtures cover 8,176 cases and detect
  missing-header/erased-archive mutants. Lean controls retain full 37-step
  execution, empty-field framing, absent input and malformed-input rejection.
  Targeted and root builds pass; all 782 public computational axiom reports
  use standard axioms only. The warning-free 60-page reference has §14.41 on
  page 58; every changed page was visually reviewed.

  Complete record framing now checks in `RecordParserMachine.total_run`:
  initial count parsing, repeated calls, later-field failures, zero/exhausted
  counts and trailing-input rejection all execute in the same six-stack program.
  On success it restores the complete original word, including the count header.
  If L is raw input length and U(B,h)=3B+16+(B+1)(2B+4)+2h, the bound is
  3L+4+(L+1)U(L,L). The loop conserves remaining-input plus archive length and
  charges each successful call to consumed input, including empty fields.
  `cache_run` instantiates the original cache encoding; `source_cache_run`
  derives B=cacheRecordBitBound p q (n+15) from actual source support and the
  attacker's hash budget. No external size or presentation premise is added.
  Five Lean controls check empty and multiple fields, missing/later malformed
  fields and trailing input; independent fixtures cover 8,191 raw words and
  477 structured/directed cases with three detected mutants. Targeted build
  passes. Root build and all 805 public computational axiom checks pass with
  standard axioms only. The warning-free 61-page PDF has §14.42 on page 59;
  all changed pages were visually reviewed. Milestones remain 2/3 complete;
  Step 3 active.

  `PreservingCompareMachine.run` now restores the original query and clears
  candidate/scratch on both outcomes, with exact equality flag and bound
  2*|query|+|candidate|+3. Full-key encodings derive bound 3*keyRecordBitBound p+3.
  `parser_run` instantiates a concrete seventh query stack and uses the existing
  parser output/scratch for candidate/buffer; input, count, outer and archive
  remain intact. This closes query reuse across comparisons, not entry extraction
  or the repeated scan. Four Lean controls cover restored nonpalindromic equality,
  early mismatch, both strict prefixes and surrounding parser data. Independent
  fixtures check 16,129 pairs and detect skipped-restoration/ignored-tail mutants.
  Targeted/root builds and all 815 public computational axiom checks pass
  with standard axioms only. The warning-free 62-page PDF has §14.43 on page 60;
  every changed page was visually reviewed. Milestones remain 2/3; Step 3 active.

  `CacheKeyFieldMachine.run` now executes the original E(2) pair header,
  existing field parser and preserving comparison with a derived handoff. Query,
  outer counter and archive survive; key workspace is empty; the scalar-answer
  suffix is retained. `total_run` covers every raw input, distinguishing malformed
  header/key-field framing from valid mismatch, with bound
  3L+17+(L+1)(2L+4)+2|query|. `entry_run` instantiates the original cache-entry
  codec, deriving bound 3*K.size+17+K*(2*K.size+4)+2K from K=keyRecordBitBound p.
  Four Lean controls and 30,705 raw + 2,835 structured fixtures retain suffix,
  match/mismatch, malformed framing and wrong count; both mutants are detected.
  Targeted/root builds and all 826 public computational axiom reports pass
  with standard axioms only. The warning-free 63-page PDF has §14.44 on page 61;
  all changed pages were visually reviewed. Milestones remain 2/3; Step 3 active.

  `CacheEntryMachine` now executes answer framing in the same program while
  retaining match/mismatch in finite control. `decode_original` proves equality
  to the original strict two-field decoder. `total_run` covers every raw entry
  with bound 6L+26+2(L+1)(2L+4)+2|query|, actual halt and preserved query/frame;
  malformed/missing/trailing framing rejects. `run` gives the full successful
  workspace and encoded answer; `entry_run` instantiates the original typed
  cache entry and derives key/scalar bit bounds. Five Lean controls include
  retained mismatch, empty versus missing answer, and trailing rejection.
  Independent fixtures cover 57,337 raw + 4,725 structured cases and detect
  overwritten-comparison, ignored-tail and skipped-answer mutants. Targeted
  and root builds pass; all 839 public computational axiom reports use standard
  axioms only. The warning-free 64-page PDF has §14.45 on page 62; all changed
  pages were visually inspected. Milestones remain 2/3; Step 3 active.

  `CacheLookupMachine.loop_run` now proves the repeated actual scan against
  List.dlookup, deriving the successor workspace through answer clearing and
  binary decrement. `run` includes complete cache copying and count parsing,
  agrees with AList.lookup, and preserves the exact query/original cache.
  For N entries and W encoded bits, its bound is
  2W+3*N.size+N*iterationCost(p,q,N)+8. `source_cache_run` derives N≤n+15
  and W≤cacheRecordBitBound(p,q,n+15) from actual repaired-source support and
  the attacker hash-query budget. No size/frame/adequacy certificate is added.
  Five Lean controls cover early/late hits, nonempty and empty misses, and four
  malformed frames. Independent fixtures validate 3,845 canonical and four
  malformed cases, detecting missing-copy, first-entry-only and lost-query
  mutations. Targeted/root builds and all 848 public computational axiom reports
  pass with standard axioms only. The reference resolves 438 computational
  declarations; its warning-free 65-page PDF has §14.46 on page 63. Every changed
  page was visually reviewed; upstream pins/checkouts and the symbolic secrecy
  endpoint are unchanged in this increment.
  Milestones remain 2/3; Step 3 active.

  `BitIncrementMachine.run` now executes canonical binary carry/restoration
  within 2*N.size+2 transitions, preserving surrounding stacks. The complete
  five-stack `FrameWriteMachine.run` counts actual payload bits and writes
  E(|payload|)++payload++suffix, clearing every workspace. Its bound is
  |payload|*(2*|payload|.size+5)+3*|payload|.size+5. `prefix_run` writes E(N)
  from N.bits within 3*N.size+3; `key_field_run` and `scalar_field_run` derive
  full operand bounds from existing codecs. Eight Lean controls retain carry,
  zero, nonpalindromic data/suffix and length-boundary behavior. Independent
  fixtures cover 1,028 increments (including 257-bit carry) and 6,141 fields;
  broken-carry, reversal and omitted-delimiter mutants are detected. Targeted/root
  builds and all 864 public computational axiom reports pass with standard axioms
  only. The reference resolves 448 computational declarations; the warning-free
  66-page PDF has §14.47 on page 64, with every changed page visually inspected.
  Milestones remain 2/3; Step 3 active. This supplies a required writer, not complete cache insertion.

  `CacheLookupMachine.miss_run` now derives the full empty workspace after an
  actual complete miss. `CacheInsertMachine.run` executes guarded insertion in
  nine stacks: lookup, old count parsing/increment, scalar/key copying and field
  writing, original E(2) pair header, whole-entry framing and new outer count.
  It requires no supplied freshness, workspace, complete-entry encoding or cost
  certificate. Occupied keys preserve the cache; a fresh key gives the original
  AList.insert encoding and all operands survive. `source_cache_run` derives
  the bound from actual supported repaired caches and the n+15 entry/bit bound.
  `programmed_cache_run` matches the original programmed source's cache and
  sticky collision flag, including equal-answer collisions; it does not yet
  execute transcript sampling/construction or the statement-history list.
  Five Lean controls and 11,535 canonical plus four malformed fixtures cover
  literal prepend order, empty insertion, head/late collisions, agreeing answers
  and rejection. Five mutations are detected. Targeted/root builds and all 875
  public computational axiom reports pass with standard axioms only. The
  reference resolves 457 computational declarations; the warning-free 67-page
  PDF has §14.48 on page 65, with every changed page visually inspected.
  Milestones remain 2/3;
  Step 3 active. General replacement remains distinct: AList replacement moves
  the new pair to the front and erases the old occurrence; actual finite source
  handlers insert only after misses, so no replacement scan was added.

  `CacheHashHandler` now uses fixed-fuel runs of the actual lookup/insertion
  machines, with fuel derived from loaded word length and entry count bounded
  by framing. `hash_eq` preserves the actual logged hash branch's complete
  OracleComp syntax. `run_eq` extends this to every source program and arbitrary
  initial typed cache/log, preserving requests, outputs, encoded successor
  caches and ordered logs through every continuation. Hits return without
  entropy; misses request the original wrapped challenge before insertion and
  append the original log entry. Explicit machine failure is unreachable on
  canonical source states, as derived by the equality. No source-correspondence
  premise is added. The insertion's second deterministic lookup is included
  in its bound and does not add an oracle request.
  Four Lean controls exclude eager resampling and immediate miss returns and
  retain literal hit/miss output and log order. Independent fixtures check
  1,728 branches and 2,187 three-request sequences, detecting four mutations
  with zero failures/gaveUp. Targeted/root builds and all 885 public
  computational axiom reports pass with standard axioms only. The reference
  resolves 467 computational declarations; the warning-free 68-page PDF has
  §14.49 on page 66. Every changed page was visually inspected.
  Milestones remain 2/3 complete; Step 3 active.

  `LogAppendMachine.run` now executes chronological record append with a
  retained key and empty workspace. `log_run` covers the exact original log
  codec; `source_log_run` derives entry/bit bounds from supported repaired-source
  executions and the n+15 hash budget. The machine parses/increments the count,
  copies/frames the key, transfers the old body in order and writes the new count.
  The bound includes every control transfer. Five Lean controls and 3,905
  structural plus six boundary fixtures retain append order, repeated entries,
  binary count growth, zero fields and key preservation; five mutations are caught.
  `FrameWriteMachine.scalar_prefix_run` reuses the existing writer to encode
  a scalar from loaded canonical digits within 3*(q-1).size+3 transitions;
  zero/nonpalindromic controls and 108 prefix fixtures retain the original format.
  No new scalar machine or changed codec is introduced.
  The existing `CacheHashHandler` now stores the log as bits, runs that append
  after insertion and executes scalar-prefix writing before insertion.
  `append_encode` and `scalarWord_encode` discharge the new calls; `hash_eq` and
  `run_eq` retain exact source query trees, outputs and both encoded successor
  states for every source program. Four existing driver controls are preserved
  at the encoded-log interface. Updated independent fixtures check 1,728 branches
  and 2,187 three-request sequences carrying actual cache/log words and sampled
  scalars 0/1/6 modulo 11, with four detected mutations and zero failures/gaveUp.
  Targeted/root builds and all 900 public computational axiom reports pass
  with standard axioms only. The reference resolves 480 computational
  declarations; the warning-free 69-page PDF has §14.50 on page 67 and the
  updated driver theorem on page 66. Every changed page was visually inspected.
  Milestones remain 2/3 complete; Step 3 active.

  `CacheLookupMachine.hit_run` now derives the complete parser workspace and
  archived scalar from the actual scan. `CacheReadMachine.run` links the existing
  parser on those same eight stacks, requires full scalar-field consumption and
  returns canonical digits with zero distinct from a miss. Query/original cache
  are retained. Its bound adds 3*(q-1).size+5 to lookup; `source_cache_run` derives
  the n+15 entry/bit bounds from actual repaired-source support. The existing
  driver's `probe_encode` uses that executed parse; `hash_eq`/`run_eq` retain exact
  original source request trees, outputs and both encoded successor states.
  Numeric interpretation/range checking reuse bitsValue and remain host operations.
  Four Lean controls and 3,845 canonical plus four malformed fixtures retain
  digits, zero/miss distinction and rejection; five mutations are detected.
  Updated driver fixtures retain 1,728 branches and 2,187 triples with four
  detected mutations, zero failures/gaveUp. Targeted/root builds and all 911
  public computational axiom reports pass with standard axioms only. The reference
  resolves 490 computational declarations; its warning-free 70-page PDF has
  §14.51 on page 68. Every changed page was visually inspected. This increment
  is integrated/audited; milestones remain 2/3 complete, Step 3 active.

  Remaining C6 dependency after the C5 interface decision: obtain/load canonical
  scalar digits and implement numeric
  interpretation/range checking and physical transfers in the driver's execution interface. Scalar
  prefix writing and chronological append are checked; a.val.bits remains a
  host conversion and is not a freely justified machine input. Retain the exact
  request schedule and derive the boundary from the actual sampler/attacker
  representation, with no caller-supplied conversion or cost certificate. The driver uses OracleComp suspension and
  host continuations, not a complete oracle TM. Plain TM2 has no oracle
  instruction. Derive physical transfer/fuel-loop costs and connect the existing
  fair-bit sampler without changing the original law or dropping its statistical
  loss. Then complete initial operand loading and arithmetic/saved-context
  execution. Source-generated caches carry group/scalar membership and unique
  keys; exact successor encoding preserves this without a caller invariant.
  Internal caches are not externally supplied raw words: do not add repeated
  semantic validation unless required by the execution interface, or claim
  arbitrary raw typed-cache decoder agreement from these results.
  Determine the raw-input checks required by the attacker/execution interface;
  do not assume an arbitrary raw decoder runs correctly or add caller-supplied
  cache-validity/adequacy certificates. Record framing alone does not execute the
  full typed cache decoder. Preserve immediate rejection on exhausted input and
  binary counts. Then complete the
  operand/continuation execution-cost interface. The sampler's bit-query count
  is q.size+s for a requested range q; the full extractor's local execution and
  operand-width costs remain to be derived. The original ideal protocol law,
  public observations, rejection and freshness stay fixed. Do not replace the
  sampling error by exact equality or suppress it in later reductions. Pinned `unifSpec`
  accepts an arbitrary natural range index with answer type `Fin (n+1)`.
  Preserve the checked count-only counterexample; derive necessary operand costs
  through the concrete attacker/machine representation, without adding a
  caller-assumed operand/adequacy certificate. The saved tape contains no continuation function,
  but decoding still traverses the original OracleComp and reconstructs typed
  continuations. Implement and cost that execution; do not serialize an entire
  branching computation tree.
  Use the checked lookup/insertion bounds while deriving encoded local-operation
  costs for saved contexts, arithmetic and extraction. The concrete backend inspection confirms a material gap: pinned
  VCVioComplexity has small exact machine canaries but no general oracle compiler
  or adequacy theorem, and its generic machine composition is not inhabited.
  `IsOraclePPTBy` alone is backend-relative. Preserve pins; compare a narrow
  concrete implementation/correspondence route before any substantial backend
  layer. Do not substitute a caller-assumed local-cost or adequacy certificate.
  Then thread earlier/interleaved attacker queries and the complete public
  election interface. These are required for
  adaptive multiple-statement extraction, retaining commitments, distinct
  challenges and all losses. `strongBallot_adaptive_extract` remains planned;
  the selected post-prefix bound does not discharge that full obligation. Integrate
  the shared oracle with trustee proofs and the full election attacker/game:
  `BallotAdversary` still uses `ProbComp` and `repairedBallotSecrecyGame` takes
  explicit hash functions. Preserve all hash inputs and attack/repair controls.
  The reference simulator's
  nonzero-sampling loss must remain in the final bound. A Schnorr signature
  EUF-CMA theorem is not adaptive ballot-proof extraction. Connect the resulting
  witnesses to arbitrary accepted ballots, complete trustee publications and
  rejection in the secrecy game, then the DDH reduction and its efficiency and
  security-parameter bounds. Current fixed three-voter attack/correctness
  instances do not discharge parametrized election-size or corruption coverage.
  These construction/reduction obligations remain open; no missing ballot
  correspondence is to be added as a security assumption.

## 5. Follow-on work after the Helios milestone

### Retrospective reuse audit after B1–B10

- [x] Add missing CSLib, SymbolicCryptographyLean and Isabelle AFP Git reference
  submodules; preserve existing LeanDY, VCVio and CatCrypt-core pins. Inspect
  the relevant transition, frame/binder, attacker and symbolic-soundness
  interfaces. Evidence: [source exploration](docs/research/helios-reuse-source-exploration.md)
  records exact revisions, declarations, compatibility gaps and source-only
  verification scope. That initial exploration was source-only; subsequent selected CSLib builds and
  adapter proofs are recorded in the retrospective below.
  The [companion symbolic-soundness paper](_references/dziembowski-fabianski-micciancio-stefanski-2025-symbolic-cryptography-lean.pdf)
  (ePrint 2025/1700) is saved and linked in the exploration, including its
  expression-language scope and explicit polynomial-time assumptions.
- [x] After B1–B10 are complete, assess how much of the finished development
  could have reused existing work. Freeze the completed theorem/dependency
  snapshot and map our actual modules/obligations to pinned upstream
  declarations. Cover CSLib, LeanDY, SymbolicCryptographyLean, Isabelle
  Psi-calculi and the already inspected computational libraries where relevant.
  Classify direct reuse, small adapters, major extensions, cross-prover ports
  and unmatched work; include the ProVerif voting framework as a design
  comparison with its homomorphic-tally limitation explicit.
- [x] Validate representative reuse candidates in isolated projects with their
  pinned toolchains. Prove the adapters preserve the completed theorem's
  assumptions, public observations and action semantics; audit imported theorem
  axioms and retain positive/negative controls. Start with CSLib weak-bisimulation
  composition and an Isabelle-inspired binder/frame lemma. Record failures and
  adaptation costs rather than treating source similarity as demonstrated reuse.
- [x] Produce a quantified reuse report: gross overlapping modules/lines and
  net removable work after adapters, with proof sources, controls, audit
  scaffolding and comments separated and shared dependencies counted once.
  Distinguish demonstrated substitutions from estimates, identify upstream
  availability at project start, and report effort measurements only where
  supported. Explain which original work remains necessary; do not derive time
  savings or an avoidable-work percentage solely from raw line counts.

  Completed 2026-09-12. Evidence: [retrospective report](docs/research/helios-reuse-retrospective.md),
  frozen dependency hashes, checked native CSLib composition, actual-source
  integration on the main toolchain, and an independent Lean port of AFP frame
  freshness. The AFP experiment is a cross-prover port, not an Isabelle runtime
  build. One copied CSLib proof line needs a Mathlib-version adaptation. All
  checked adapter axioms are standard; complete actions and full observations
  remain explicit. The exact 9-code-line frame proof can be replaced by 13
  code lines; the generic B10 candidate scope is 44 code lines, with no checked
  deletion. No positive net removal is demonstrated; broader savings and
  development-time savings are unmeasured. Main sources, manifest and upstream
  pins/checkouts are unchanged. The requested post-secrecy audit is complete.

### Reusable election framework and symbolic-to-computational bridge

Source: [Simultaneously Proving Privacy and Verifiability: A ProVerif
Framework for Internet Voting](_references/cheval-cortier-debant-moser-2026-privacy-verifiability-proverif.pdf),
[HAL version 2](https://inria.hal.science/hal-05587654v2).
Status: **staged** follow-on work. Historical B1–B10 and computational 3/3
proof milestones are complete under their documented boundaries; publication is
complete. Framework implementation and transfer proofs have not started. These tasks do not reopen B1–B10 or
change the acceptance conditions of the concrete secrecy milestone.

Discussion update, 2026-09-12: recorded
[a Lean election language with computational soundness](docs/research/election-computational-soundness-idea.md)
as a **staged research idea**. It proposes shared symbolic/computational semantics,
a conjectured privacy-transfer theorem, explicit admissibility and primitive
assumptions, and concrete Helios attack-and-repair evidence before generalization.
The user has requested discussion and documentation only; implementation remains
unstarted. This direction extends the architecture discussion below; it is not
the already completed symbolic source-correspondence theorem. The note also
records literature precedents, the homomorphic-tally gap and an accepted-ballot
definition counterexample as future evaluation context. Development priorities
remain in this task list.

Planning update, 2026-09-13: incorporate Baloglu, Bursuc, Mauw and Pang,
[Election Verifiability in Receipt-free Voting Protocols (CSF 2023)](https://satoss.uni.lu/members/jun/papers/CSF23.pdf),
alongside the 2026 framework. The former supplies definition and adversary-model
checks; the latter supplies shared-model architecture and symbolic automation.
Neither establishes the intended computational privacy transfer. Theorem 1 of
the 2023 paper connects verifiability predicates on traces; the 2026 model
transformations also remain symbolic. Evidence: literature analysis and the
[updated design note](docs/research/election-computational-soundness-idea.md#lessons-from-the-2023-and-2026-verifiability-frameworks);
all new proof obligations below are **staged**, not machine-checked.

Scope update, 2026-09-16: reconstruct the CSF 2026 election framework and its
proof principles in Lean, with **ballot privacy, receipt-freeness and end-to-end
verifiability** as separate properties over a shared semantics. Research question:
can reusable checked arguments expose exactly which protocol restrictions and
trust assumptions make these properties compatible? BeleniosRF and SeleneRF are
candidate cases, not presumed secure instances. The
[research note](docs/research/election-computational-soundness-idea.md#receipt-freeness-scope-and-candidate-instances)
records literature boundaries and proposed falsifiers. Discussion/documentation
only is authorized here; no framework implementation goal is active.

- [ ] Specify symbolic receipt-freeness separately from ballot privacy and
  stronger coercion resistance: disclosure timing/content, private channels,
  corruption, admissible contexts, and the quantifiers over voter strategies.
  Require intended-vote success as well as indistinguishable adversary views.
  Retain a receipt-producing counterexample and an independently justified
  restricted successful example; do not infer receipt-freeness from privacy.
- [ ] Test the common interface against BeleniosRF and SeleneRF, including
  separate casting/verification credentials, rerandomization, trackers and
  verification after tallying. Reproduce the CSF 2023 BeleniosRF verifiability
  attack under its stated assumptions. SeleneRF receipt-freeness remains a
  candidate theorem; the cited paper leaves its stronger guarantee unproved.
  Computational transfer and full coercion resistance require separate results.

- [ ] Specify the common election interface and resolve the differences in the
  [existing scope comparison](docs/research/helios-scope-comparison.md). Compare the historical symbolic repair
  with the selected computational repair: proof/context binding, identities and
  credentials, corruption and key generation, network scheduling and dropping,
  revoting, acceptance/rejection, trustee behavior, challenge admissibility and
  every public output. Cite actual definitions and classify each difference as
  matched, restricted, changed, or unresolved. A changed repair requires its own
  symbolic instance or a proved applicable relation; do not presume equivalence.
- [ ] State the narrow privacy bridge before generalizing the language. Separate
  protocol/model correspondence from cryptographic soundness. Specify the
  security parameter, permitted leakage, all-PPT attacker quantifier, primitive
  assumptions, independently checkable admissibility and quantitative loss.
  Require preservation of two-world observations; ordinary trace inclusion alone
  is insufficient. Identify which existing theorem would supply each premise.
  The statement remains conjectured until its Lean proof is checked.
- [ ] After the concrete Step 3 case study, prove the narrow bridge and its
  application to an explicitly aligned repaired Helios instance. Prove the
  required correspondence rather than accepting it as a caller assumption.
  Account for malformed accepted inputs, extraction/simulation, collisions,
  sampling, homomorphic tallying and runtime. Keep general language soundness
  separate from both this instance and the symbolic transfer task below.
- [ ] Add model-alignment regression controls before claiming bridge coverage:
  shared credentials, a dropped ballot with apparent successful verification,
  leaked versus adversarially chosen keys, and a public-output privacy leak.
  Use the 2023 BeleniosRF clash attack as a definition-level control where its
  assumptions apply; do not label it an attack on our scoped Helios game.
  Retain separate verifiability and two-world privacy assertions. Any excluded
  corruption/network scenario must appear in the theorem's scope. Keep private
  proof extraction distinct from public operations and efficient reduction code.

The paper's framework excludes homomorphic tallying (§IV-E). Its Helios-like
example uses an identity-binding ballot proof and a decryption shuffle
(§II-B, §VII-B), so it does not directly instantiate our historical
component-weeding repair. Use its architecture as a reference; establish each
adapted obligation for our equations, observations and rejection behavior.

- [ ] Extract a reusable source-correspondence/bisimulation transfer theorem
  from the completed B9/B10 proof. State the relation, observation preservation,
  internal and visible transition matching, freshness and successor-closure
  obligations explicitly. Instantiate it with historical Helios and retain a
  negative control for an observation-changing transformation. The paper's
  tally-swap and query-translation soundness arguments (Appendices C–D) motivate
  this task; they are not an existing Lean transfer theorem.
- [ ] Package accepted-ballot provenance and cross-world contribution invariants
  behind a proved interface, using our reconstruction and acceptance results.
  Compare with the paper's `cellBB` lemma (§V-E), without assuming its
  identity-binding or predictable-cell hypotheses for component weeding.
  Keep proof-only plaintext extraction separate from public attacker operations.
  Retain an accepted honest case and a replay/malleation counterexample for an
  appropriately weakened repair.
- [ ] Specify one authoritative election execution model for privacy and future
  verifiability proofs (§III–IV). Share board, acceptance, trustee and public
  output definitions; justify property-specific instrumentation and abstractions.
  State verifiability separately, including eligibility, verification events,
  multiplicity and completion conditions. Do not infer it from ballot secrecy.
- [ ] Consolidate public-observation controls for identity-ordered vote release,
  premature trustee publication, omitted transcript fields and equal-tally-only
  privacy arguments. Reuse existing controls where applicable; add independently
  derived positive/negative fixtures where missing. Record exactly which
  observable distinguishes each mutated model. The ordered-tally privacy failure
  in §III-B supplies an external motivating example.
- [ ] Separate generic election/process infrastructure from protocol-specific
  ballot validity, cryptographic equations and tally laws (§III-B). Require
  checked interface laws for every instance. Preserve historical Helios as the
  homomorphic instance, with its source correspondence and explicit assumptions.
- [ ] After the concrete computational theorem, evaluate reuse through one small
  second application before claiming a reusable framework. Record adapters,
  changed assumptions, new obligations and actual adaptation costs; broad
  refactoring and election-language/transfer work stay deferred until the concrete
  case is complete. A candidate is the identity-bound shuffle election below.
- [ ] Evaluate reuse with a second, small identity-bound shuffle election,
  inspired by §VII. Record reused and newly required definitions/proofs,
  assumptions, adaptation effort and reproducible build/verification timings.
  Include a checked attack after weakening the relevant protection. Compare
  against a ProVerif case study only after documenting model correspondence;
  report prepared-model verification time separately from development effort.

### Other follow-on work

- [x] Add [references.md](references.md), an annotated index of all eight local
  papers in `_references/`, and link it from the README (2026-09-14). Checked
  titles/authors against local PDFs and validated local links and PDF coverage.
  Relevance notes distinguish source results from our checked scope.

- [x] Download Greenman, Saarinen, Nelson and Krishnamurthi,
  [Little Tricky Logic: Misconceptions in the Understanding of LTL](_references/greenman-saarinen-nelson-krishnamurthi-2023-little-tricky-logic.pdf)
  ([arXiv:2211.01677](https://arxiv.org/abs/2211.01677)), for experiment-design
  reference (2026-09-14). Validated PDF header and successful text extraction.
  Its specification-reading, specification-writing and trace-judgment tasks,
  formative misconception collection and response coding inform study design;
  this is literature context, not evidence that our intervention improves learning.

- [ ] Revisit [mutation automation ideas](docs/mutation-testing-ideas.md): typed
  mutation syntax, witness search and proof-carrying classifications. Derive
  coverage from certificates and keep failed searches unresolved.
- [ ] Extend the foundations and TLS work only after recording the library
  decision and completed Helios scope. Keep the proposal's planned deliverables
  distinct from the implemented theorem catalogue.

### Development CI (2026-09-14)

- [x] Add `.github/workflows/check.yml` for root Lean build, symbolic and full
  computational axiom audits, reference/type checks, PDF compilation and independent
  fixture campaigns, retaining logs and rebuilt PDF artifacts.
- [x] Confirm a corrected hosted CI run: `34810204996` (historical private-repository run)
  at `814f557` passed both jobs, including Lean/audits/PDF and independent controls.
  Visual PDF review remains a publication requirement.

First hosted run: independent fixture campaigns passed. The Lean/reference job
failed before Lean setup because the runner could not authenticate to the skills
repository. PDF compilation now invokes installed Tectonic/latexmk directly;
research skill instructions and upstream pins are unchanged. The corrected hosted
build/audit is confirmed above; later commits have their own workflow results.
