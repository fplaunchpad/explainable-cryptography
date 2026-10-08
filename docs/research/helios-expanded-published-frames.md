# Individual handles for published partials and results

Status: **machine-checked exact presentation equivalence and minimum origins**.
The expanded frame retains the three initial handles and exposes each candidate
partial and result individually. It has exactly the same public observations
as the actual final tuple frame. This is a proof presentation; the protocol
continues to publish the complete tuples defined in
[published frames](helios-published-frames.md).

## Public translations

`expandedFrame` has `3 + (n+1) + (n+1)` handles: the original three, followed by
all candidate partials, followed by all candidate results. `expandedOld`,
`expandedPartial` and `expandedResult` define the typed slot indices.

`expandedRecipes` projects each slot from the actual five-handle final frame.
`tupleRecipes` reconstructs the original two complete ordered tuples and
retains the original handles. Both recipe families are public for every
restricted-name policy. Their evaluated values equal the corresponding frame
values under E. These identities require no acceptance, freshness or
submission-publicness premise.

`expanded_frame_staticEq_iff_final` uses both public translations to prove
that static equivalence of the expanded swapped frames is equivalent to static
equivalence of the actual final swapped frames. Public submission recipes then
allow `expanded_frame_staticEq_iff_partial` to compose the existing final/partial
criterion. Neither theorem asserts that either pair of swapped frames is
already equivalent.

`expanded_old_recipe_value` preserves arbitrary initial recipe values exactly.
The existing final-frame name invariant transfers through the public
translation as `expanded_frame_opaque_protected`, for public submissions.

## Minimum recipes in the expanded frame

Every handle recipe has one node. `Frame.minimum_handle_value_size_one` proves
that any minimum public recipe equal to an existing handle value also has one
node. Applied to the expanded frame, this gives the bound for every published
partial and every actual result expression. The latter may represent a large
numeral, so a literal numeric recipe need not supply the useful size bound.

`expanded_decryption_not_minimal_of_result` excludes a minimum decryption whose
value is an already-published result. `expanded_bound_tally_decryption_not_minimal`
applies this when the key and ciphertext values are the corresponding trustee
partial and complete tally binding. `expanded_minimum_decryption_no_trustee_E6`
derives that binding from semantic E6 matching with a borrowed trustee partial.
These results have explicit value premises and do not exclude structured-key
E5 against newly constructed ciphertexts.

For fresh names and an accepted finite public submission sequence,
`expanded_minimum_trustee_partial_origin` proves that any minimum recipe for a
published trustee partial is a partial-slot handle. Names and constants have
the wrong shape; the initial handles cannot reconstruct trustee partials;
result handles are numeric. The conclusion records both the source slot and
E-equality of its complete binding to the requested candidate binding. It does
not assume unique partial-slot values or silently discard possible aliases.

Minimum size is measured within this expanded frame. Public translation does
not preserve node counts. A checked control gives the same partial observation
through a two-node tuple projection and a one-node individual handle. The
remaining proof must establish expanded-frame equivalence and transport that
result through the exact criterion, rather than transport minimality itself.

## Evidence and controls

Artifacts:

- [Frame definitions](../../ExplainableCrypto/Helios/Symbolic/ExpandedPublishedFrames.lean).
- [Public translations and equivalence](../../ExplainableCrypto/Helios/Symbolic/ExpandedFrameEquivalence.lean).
- [Minimum origins and shortcuts](../../ExplainableCrypto/Helios/Symbolic/ExpandedMinimumOrigins.lean).
- [Ten SPOTs](../../ExplainableCrypto/Helios/Symbolic/ExpandedFrameSPOT.lean).
- [Executable gate](../../ExplainableCrypto/Helios/Symbolic/ExpandedFrameExperiments.lean).

The controls cover both complete translations, independently unequal zero/one
result slots, omission of the last partial under full E, minimum partial-slot
origins, a wrapper refuting omission of the minimum premise, actual E6 tally
computation with a result shortcut, a nonempty tally of two with a one-node
handle, unequal translation costs, public structured-key E5 and an inhabited
diagonal equivalence criterion with distinct public names.

The gate detects shifted-result and omitted-last-partial defects at input 0,
seed 1, zero shrinks. Seeds 1, 7 and 42 each pass 500 cases, size 40, `gaveUp=0`;
2048 deterministic inputs pass. It checks both translations on one/two
candidates, nonliteral candidate values, zero through five submissions, and
both assignments. Log: `tmp/variable-overlap/expanded-frame-gate.log` (1013 jobs).
Raw normalization supplies only this bounded executable check; the translation
identities and minimum claims are proved under the full theory E.

B8 remains open. General origins for arbitrary extended-frame values and all
cross-world recipe equality observations still need proof. B9 process matching
and B10 symbolic secrecy also remain open. The
[blueprint](helios-proof-blueprint.md) records this exact residual scope.

Full `lake build` passes **3631 jobs**, with **1882 nonempty standard-only
axiom reports**, **20 axiom-free reports**, **916 public theorem entries** and
**49 current-status documents**. Twenty-eight new theorem audits include ten
SPOTs; seven definitions are checked. Log:
`tmp/variable-overlap/expanded-frame-full-build.log`.

Initial failures were proof engineering: unrestricted Fin simplification
changed the index form needed by the eliminator, and handle values needed
explicit simplification in the minimum proof. The declaration scanner also
mistook a comment line beginning with “theorem” for a declaration; rewording
the comment removed that false audit entry. No protocol rule, value premise
or target theorem was weakened.
