# Expanded public decryption and trustee binding

Current status (2026-09-11): [B8 is complete](helios-published-static-equivalence.md).
The full partial/final-frame static-equivalence theorems discharge the binding
and local-induction premises left open in this record's historical checkpoint.
B9 process matching and B10 labelled bisimilarity remain open.

Status: machine-checked case reduction; integrated build and audit complete. B8 remains
at 11/12 local operator cases and 7/10 top-level milestones. Successful
ordinary E5 and E6 with a publicly constructed partial are now discharged.
The remaining case is E6 with a published trustee partial, where a minimum
ciphertext recipe must retain its complete tally binding across assignments.
B8, B9 process matching and B10 symbolic secrecy remain incomplete.

[ExpandedPublicDecryption.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedPublicDecryption.lean)
proves `expanded_minimum_ciphertext_public_secret_form`: a minimum ciphertext
encrypted to a publicly denotable secret has raw `penc` syntax. Its premises
are public submissions, numeric source results, minimum ciphertext and public
secret recipe. No freshness or minimum-secret premise is needed. A minimum
constructed-only group compresses to a raw constructor. An honest or mixed
group would identify its public secret recipe with the restricted election
secret; expanded-frame opaque protection excludes that possibility.

`public_key_constructed_decryption_transfer` is generic over frames and handle
counts. Direct E5 needs one smaller public-key comparison and retains a
published structured partial as a legitimate ordinary secret. The generic
`public_partial_constructed_decryption_transfer` reuses the existing three
key/binding probes. Its E5 alternative remains present alongside bound E6.
Both theorems preserve the actual explicit plaintext recipe, which can denote
a different public ballot in each voting world.

[ExpandedTrusteeBinding.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedTrusteeBinding.lean)
assembles the exhaustive successful-decryption split. Direct E5 supplies a
public secret; constructed E6 supplies the first argument of its minimum
partial constructor. The theorem above gives raw ciphertext syntax in both
cases, and the plaintext child is globally minimum. Borrowed E6 has an exact
published-slot origin and binds the entire tally ciphertext. Its result is
represented by the corresponding one-node published result handle.

The remaining proposition is explicit:

```lean
ExpandedTrusteeBindingTransport ns swap swap' left right rs
```

For every slot `j` and source-minimum ciphertext recipe `b`, it asks that
`eval b =E tallyCiphertext ... j` transfer to the other assignment. Its two
induction premises are shared minima in both directions for recipes strictly
smaller than `dec (var (expandedPartial j)) b`. They use the original bound;
there is no additional allowance for a result probe or an oversized explicit
tally comparison. The publicness of `b` follows from its minimum hypothesis.

`accepted_expanded_minimum_children_decryption_shared_of_trustee_binding` closes
both successful and stuck decryption conditional on that proposition.
`accepted_expanded_successful_decryption_of_trustee_binding` supplies the former
residual interface. The three `accepted_*_staticEq_of_trustee_binding` theorems
connect it to expanded, aggregate-partial and actual final static equivalence,
requiring fresh names, public accepted submissions, valid candidates and both
binding-transport directions. No separate public E5, public E6, checking,
observation or global common-minimum premise remains. General binding transfer
for nested new-handle ciphertext recipes is still unproved.

`expanded_old_tally_binding_swap` already proves full binding transfer for
every retained old public recipe, using B7. It needs neither minimum size nor
acceptance nor smaller observations. The initial frame evaluates the complete
public tally recipe, so this is a full-ciphertext equality argument, not an
argument from equal numeric tallies. `expanded_bound_tally_shared` then shares
the actual result slot when both bindings are supplied.

[ExpandedSuccessfulDecryptionExperiments.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedSuccessfulDecryptionExperiments.lean)
checks reachable empty-submission frames for one through five candidates and
both assignments. Actual trustee partials serve as E5 secrets and as inner
secrets of publicly constructed E6 partials. Plaintexts include result handles
and pairs containing an honest ballot and a published partial. Actual borrowed
full-tally decryptions are also checked. The independent oracle uses direct
constructor reductions and the literal full-tally recipe, not the classification
theorem. Omitting structured E5, erasing complete E6 binding, and assuming every
successful ciphertext is a raw constructor all produce the intended input-zero
counterexample at seed 1, zero shrinks. Seeds 1/7/42 each pass 500 cases at size
40 with `gaveUp=0`, and all 2048 deterministic inputs pass. Raw normalization in
these bounded fixtures is not a complete E/E0 decision procedure or evidence
of general privacy. The gate build passes 1061 jobs.

[ExpandedPublicDecryptionSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedPublicDecryptionSPOT.lean)
contains eight kernel controls:

- A seven-node E5 decrypt has actual minimum children and uses a published
  trustee partial as its secret, returning an honest ballot handle in both worlds.
- A thirteen-node public E6 decrypt uses that partial as its inner secret and
  preserves the full ciphertext binding and explicit ballot plaintext.
- Borrowed E6 consumes a globally minimum five-node honest product, refuting
  the initial-frame all-constructed classification after publication.
- The aggregate partial cannot decrypt just one honest component: E5 would
  expose the secret, while E6 would erase an occurrence from the tally binding.
- B7 transfers a retained old tally recipe even with a removable wrapper.
- Such a wrapper refutes raw-constructor origin without the minimum premise.
- A nonempty accepted submission sequence publishes two; the actual full-tally
  decryption shares its one-node result handle in both assignments.
- Equal-candidate frames inhabit both residual binding premises and exercise
  the full conditional local/global pipeline in all three frame presentations.

The generic transfer controls use inhabited diagonal observations; their direct
semantic controls also cover different-vote worlds. The pipeline control does
not establish arbitrary-candidate B8. Existing key and binding negative controls
remain imported. Targeted builds pass: public decryption 972 jobs, residual
binding/assembly 992 jobs and controls 1125 jobs. Initial failures were Lean
layout and publicness elaboration, with no weakened theorem or equation change.

See the [proof blueprint](helios-proof-blueprint.md),
[results ledger](helios-results.md) and
[preceding successful-check checkpoint](helios-expanded-successful-checks.md).

Integrated evidence: full `lake build` passes 3751 jobs. Eighteen new public
theorem audits give 1400 covered entries across 73 current-status documents.
The log contains 2365 nonempty reports using only `propext`, `Classical.choice`
and `Quot.sound`, plus 21 axiom-free reports. All six changed Lean modules have
current oleans and no proof holes or custom axioms. All 932 local links resolve;
no warnings/errors appear in the build log, and `git diff --check` passes.
Log: `tmp/variable-overlap/expanded-public-decryption-full-build.log`.

[Result-handle realization](helios-result-handle-binding.md) now transfers full
tally bindings for all public old-plus-results recipes, including nested uses,
without size or minimum hypotheses. Only minimum ciphertexts without a
result-only presentation remain in the trustee-binding callback. A checked
ten-node minimum result-nonce recipe refutes old-only syntax and grows to
fourteen nodes under numeral realization.
