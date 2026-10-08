# Name protection after partial and result publication

Status: **machine-checked**. Every public recipe over the actual partial frame
fails to deduce a restricted name. The same holds for the final frame when
submissions are public. This includes arbitrary nested uses of the new handles.
The result supplies a necessary invariant for B8's extended recipe analysis;
[partial-frame static equivalence](helios-proof-blueprint.md) remains open.

## Invariant and proof

`Term.opaqueSafe` is a metatheoretic predicate, not a new protocol rule. It
allows restricted names inside pk, spk and partialDecrypt because the encoded
signature has no field-extracting destructor for those constructors. It checks
ciphertext keys and plaintexts, all pair fields, and every exposing operation.
E6 obtains plaintext from its separately supplied ciphertext; making a partial
opaque does not exempt that ciphertext's plaintext from the check. E5 also
remains available for ciphertexts keyed by a partial.

The predicate is preserved by E0 equality and forward reductions in any
context, including reductions modulo E0. Public substitution preserves it.
Confluence then excludes equality between a protected term and a restricted
name. This proof uses the existing full theory E and its confluence theorem;
it does not treat raw normalization as a full-E decision procedure.

`OpaqueProtectedValue restricted t` requires some E-equal protected
representative. This value property is invariant under E, while the raw
predicate is not: E expansion can add an irrelevant restricted-name occurrence
under a discarded pair field. `Frame.OpaqueProtected` requires a protected
value at every handle. Public substitution of protected values proves the
invariant for every public recipe, with no bound on recipe size or nesting.

The old `nonceSafe` predicate and its results stay intact. Its stricter
protection implies the new invariant. Existing initial-frame bit
representatives therefore handle arbitrary valid ground candidate syntax,
including raw-unsafe but semantically valid expressions.

The composed-name extension reuses the existing persistent name-factor
analysis. A protected recipe cannot equal a target containing a restricted
outer composition factor, even when the target's remaining factors reduce.
This preserves the multiplicity-sensitive nonce reasoning needed by the
ciphertext analysis.

## Actual frame theorems and assumptions

| Declaration | Scope and assumptions |
| --- | --- |
| `initial_frame_opaque_protected` | Initial historical frame, either assignment, every positive candidate count and valid ground candidates; no freshness premise. |
| `partial_frame_opaque_protected` | Actual initial frame plus the complete trustee-partial tuple; arbitrary submission syntax and bindings, with no publicness or acceptance premise. |
| `final_frame_opaque_protected` | Actual final frame; public submissions suffice because the result tuple equals a public computation from the partial frame. No acceptance or freshness premise. |
| `partial_frame_name_not_deducible` | Every public four-handle recipe, every name in the full restricted policy. |
| `final_frame_name_not_deducible` | Every public five-handle recipe, every restricted name, with public submissions. |
| `partial_frame_constructed_key_not_election_key` | A key constructed from any new-frame public secret recipe cannot equal the election key. |
| `partial_frame_constructed_partial_not_trustee_partial` | A partial constructor whose first argument is a new-frame public recipe cannot equal an election-secret partial, for any binding. |

The last two results will separate constructed values from borrowed election
values in the extended recipe classification. They do not yet prove that all
possible recipe origins have been classified.

## Controls and executable evidence

Artifacts:

- [Protection definitions](../../ExplainableCrypto/Helios/Symbolic/OpaqueProtection.lean).
- [Forward closure and non-deducibility](../../ExplainableCrypto/Helios/Symbolic/OpaqueNonDeducibility.lean).
- [Composed-name exclusion](../../ExplainableCrypto/Helios/Symbolic/OpaqueComposedNames.lean).
- [Published-frame invariant](../../ExplainableCrypto/Helios/Symbolic/PublishedProtection.lean).
- [Eleven SPOTs](../../ExplainableCrypto/Helios/Symbolic/PublishedProtectionSPOT.lean).
- [Executable gate](../../ExplainableCrypto/Helios/Symbolic/OpaqueProtectionExperiments.lean).

The controls retain arbitrary nested partial-frame recipes, a public malformed
submission with no acceptance premise, availability of actual trustee partials,
a raw-unsafe valid ballot, a leaking pair publication, an E6 plaintext leak,
non-invariance of raw protection under full E, composed nonce exclusion with
arbitrary remainders, successful E5/E6 outputs, constructed-key separation and
exclusion of a nested partial constructor from trustee-partial values.

The gate catches the pair-opacity and plaintext-opacity defects at input 0,
seed 1, zero shrinks. Seeds 1, 7 and 42 each pass 500 cases, size 40, `gaveUp=0`;
2048 deterministic inputs pass. The scope includes nested opaque constructors,
pair projections, E5/E6, homomorphic multiplication, stuck operations, one/two
candidates, zero through five submissions and both assignments. Gate log:
`tmp/variable-overlap/opaque-protection-gate.log` (1005 jobs).

The trusted signature and equations remain unchanged. Restricted-name secrecy
is not vote secrecy: opaque values may still have distinguishable public
equality patterns. B8 still requires those patterns to agree for every public
recipe pair. B9 process matching and B10 symbolic secrecy remain open.

Full `lake build` passes **3626 jobs**, with **1854 nonempty standard-only
axiom reports**, **20 axiom-free reports**, **888 public theorem entries** and
**48 current-status documents**. Forty-two new theorem audits include eleven
SPOTs; three metatheory definition checks are added. Log:
`tmp/variable-overlap/published-protection-full-build.log`.

Initial failed checks were proof engineering: a reserved identifier and missing
experiment import, case splitting for binary operators in Boolean closure,
unfolding literal publicness and explicit names in factor exclusions. Neither
the protocol equations nor the candidate claim was weakened.
