# Expanded successful proof checks

Current status (2026-09-11): [B8 is complete](helios-published-static-equivalence.md).
The full partial/final-frame static-equivalence theorems discharge the binding
and local-induction premises left open in this record's historical checkpoint.
B9 process matching and B10 labelled bisimilarity remain open.

Status: machine-checked local transport; integrated build and audit complete.
B8 now has eleven of twelve operator cases closed. Successful decryption in
both directions is the only remaining local premise. B8 itself, B9 process
matching and B10 symbolic secrecy remain incomplete; top-level coverage stays
7/10, an unweighted milestone count.

[ExpandedSuccessfulCheckTransport.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedSuccessfulCheckTransport.lean)
proves `expanded_minimum_check_success_transfer` for arbitrary valid ground
candidate substitutions and either source/destination assignment. The premises
are fresh names, public submissions, numeric source results, public supplied
key, minimum ciphertext and proof recipes, and observations strictly below
the whole check's node count. There is no destination-minimum premise.

A successful proof has a minimum constructed or borrowed origin. Constructed
proofs reuse `constructed_check_success_transfer`: the supplied key, bit,
bound ciphertext and encryption-shape equalities are four smaller public
comparisons. The fourth proof argument remains bound to the entire supplied
ciphertext. This generic theorem already supports arbitrary handle types and
therefore requires no rebuilding of the cryptographic equations.

For honest proofs, `expanded_minimum_honest_combination_recipe_eqE` derives
recipe equality from the exact indexed occurrence bag of the minimum supplied
ciphertext. Its proof uses raw E0 combination equality and old-handle
substitution. The resulting equality survives every frame substitution; it
needs no possibly oversized aggregate observation. Only the supplied-key test
uses the smaller-observation premise. Retained honest component and aggregate
checks are valid for every candidate substitution, including reducible bit
representations, abstention and the one-candidate aggregate alias.

`accepted_expanded_minimum_children_check_shared_of_two_way_minima` closes both
checking cases with exactly the simultaneous induction hypotheses. Successful
checks share the one-node `ok` recipe; stuck checks reuse their existing global
minimum theorem. Accepted public submissions supply source numeric results,
and bounded two-way shared minima supply the required smaller observations.

[ExpandedSuccessfulDecryptionTransport.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedSuccessfulDecryptionTransport.lean)
reduces `Frame.DecryptCheckTransport` to `Frame.SuccessfulDecryptionTransport`.
Its three final conditional theorems yield expanded, aggregate-partial and
actual final static equivalence from successful decryption transport in both
directions. There is no separate checking, global observation or global
common-minimum premise. Those successful-decryption instances remain unproved;
this is not an unconditional final-frame privacy theorem.

[ExpandedSuccessfulCheckExperiments.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedSuccessfulCheckExperiments.lean)
checks reachable empty-submission expanded frames for one through five
candidates, honest components and aggregates, and constructed proofs whose key
and nonce use actual published partials and whose payload can use an actual
published result. Both assignments are tested. The independent expected
bindings use literal candidate sums and nonce occurrence bags. Three mutations
(wrong whole-ciphertext binding, wrong supplied key, non-bit payload) fail at
input zero, seed 1, zero shrinks. Seeds 1/7/42 each pass 500 cases at size 40
with `gaveUp=0`; all 2048 deterministic inputs pass. These raw-normalized fixture
summaries are bounded tests, not a full E/E0 decision procedure or security
proof. The gate build passes 1060 jobs.

[ExpandedSuccessfulCheckSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedSuccessfulCheckSPOT.lean)
contains nine independent kernel controls:

- An 18-node constructed check uses actual partial/result handles, has minimum
  children and shares one-node `ok` across different-vote worlds. Its diagonal
  instance exercises the new general local theorem with inhabited hypotheses.
- Changing only the fourth proof argument's nonce rejects a check with an
  actual published partial as its key.
- A nonempty accepted submission sequence publishes two; its cheap one-node
  handle still cannot serve as an accepted proof bit.
- Both voters' component and aggregate checks succeed with nonliteral votes.
- A syntactically distinct commuted aggregate has exact minimum occurrences;
  the new recipe-equality theorem transports its whole binding.
- A five-candidate aggregate costs 24 nodes; its 48-node self-comparison exceeds
  the 38-node check bound, validating the need for the origin argument.
- Distinct one-candidate component/aggregate selectors remain valid aliases.
- Arbitrary frames with minimum atomic children can lose checking success.
- Equal-candidate frames inhabit both remaining-decryption premises by minimum
  existence and yield all three conditional static-equivalence conclusions.

The last control checks the residual interface; it does not assume or establish
B8 for different candidates. The existing wrong-key kernel control is retained
through the successful-check imports. Core transport builds in 973 jobs,
residual assembly in 990 jobs and all nine controls in 1121 jobs. Initial proof
failures were elaboration details (evaluation rewrites, explicit candidate
indices and let-bound control goals); no theorem was weakened.

See the [proof blueprint](helios-proof-blueprint.md),
[results ledger](helios-results.md) and
[previous pair/selector checkpoint](helios-expanded-pair-selector-minima.md).

Integrated evidence: full `lake build` passes 3747 jobs. Nineteen new public
theorem audits give 1382 covered entries across 72 current-status documents.
The log reports 2347 nonempty standard-only axiom reports (`propext`,
`Classical.choice`, `Quot.sound`) and 21 axiom-free reports. All six changed
Lean modules have current oleans; no proof holes, custom axioms, warnings or
errors were found. All 914 local links resolve and `git diff --check` passes.
Log: `tmp/variable-overlap/expanded-successful-check-full-build.log`.

[Expanded public decryption](helios-expanded-public-decryption.md) now closes
direct E5 and constructed-partial E6. The remaining local case is complete
borrowed trustee tally-binding transfer for minimum ciphertexts. B7 handles
retained old recipes; general nested new-handle binding remains unproved.

[Result-handle realization](helios-result-handle-binding.md) now transfers full
tally bindings for all public old-plus-results recipes, including nested uses,
without size or minimum hypotheses. Only minimum ciphertexts without a
result-only presentation remain in the trustee-binding callback. A checked
ten-node minimum result-nonce recipe refutes old-only syntax and grows to
fourteen nodes under numeral realization.
