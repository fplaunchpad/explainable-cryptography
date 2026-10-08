# Source input substitution and trustee payloads

The data/substitution part of B9's source correspondence is now checked.
Capture-avoiding input substitution commutes with evaluation, private-variable
renaming preserves it, and private locals flatten to public recipes without
changing public handles. Literal source tally, trustee-reply and result
expressions agree with the actual payloads used by B8 and the twelve-stage
model. Source output frames therefore inherit B8's static equivalence under
its explicit protocol premises.

B9 remains in progress. The full source process syntax, structural/internal
semantics, restricted-channel and fresh-output-binder correspondence, and B10
labelled-bisimilarity lifting remain open. Coverage stays 8/10 (80%, unweighted).

[Historical symbolic ballot secrecy](helios-source-coordinated-phases.md)
is now machine-checked, integrated and audited. B1–B10 meet their acceptance
conditions. scopedVoterElection_ballot_secrecy proves source weak labelled
bisimilarity of the actual swapped scoped elections, for arbitrary valid ground
candidates and finite administration size under documented name, nonce/parameter
and channel freshness. SourceElectionRelation preserves all actual source actions,
complete frames, shared handle coordinates and private policies. The final
interface assumes no source correspondence, bisimulation or static equivalence.
The historical component-weeding protocol and documented tuple-tail correction,
full E/E0, attacker observations and rejection behavior are unchanged. Independent
positive/negative controls and both refuted shortcuts remain. The [retrospective reuse audit](helios-reuse-retrospective.md) is complete;
computational security is a separate extension.

## Input binding

[SourceInputBinding.lean](../../ExplainableCrypto/Helios/Symbolic/SourceInputBinding.lean)
uses `Option V` for a continuation with one fresh input variable. `none` names
the new binder and `some v` retains an old variable. `liftSubst` moves an existing
substitution past the binder while leaving `none` alone. `bindInput` instantiates
that new variable using the existing unbounded term substitution.

`bindInput_eval` proves exact evaluation agreement, `liftSubst_comp` and
`bindInput_subst` prove composition, and `bindInput_rename` handles any bijective
renaming of old variables. These laws cover every term constructor, including
opaque positions and nested destructors. `bindInput_public` preserves the
public-name policy when both the body and message satisfy it. Internal trustee
bodies can contain a secret; their correctness does not assume that they are
public recipes.

`flattenLocals` separates public handles from private locals with a disjoint sum.
`flattenLocals_eval` proves that replacing private locals by their original
public recipes preserves evaluation exactly, and `flattenLocals_public` proves
publicness under the stated local/body premises. Public and private variables
with the same numeric index cannot alias.

These are term-level laws. They do not yet prove alpha-equivalence or
capture avoidance for an entire applied-pi process or restricted channel scope.

## Private communication expressions

[SourcePayloadSyntax.lean](../../ExplainableCrypto/Helios/Symbolic/SourcePayloadSyntax.lean)
retains the source's tuple projections and input substitutions. `boardTally`
starts with the two honest ciphertext fields and folds every later input into
the product. It introduces no multiplicative identity. `trusteeBody` binds a
received tally tuple and computes a secret-keyed partial for each projected
candidate. `resultBody` binds the returned tuple and decrypts each partial
against the corresponding previously sent tally.

[SourcePayloadAgreement.lean](../../ExplainableCrypto/Helios/Symbolic/SourcePayloadAgreement.lean)
proves:

- Source input binding and payload expressions respect E-equal replacements.
- Source tallies are syntactically equal to the evaluated `tallyRecipe` tuple.
- The trustee reply is E-equal to the actual `tallyPartial` tuple.
- The substituted result message is E-equal to the actual `tallyResult` tuple.
- Every source partial/final output handle agrees modulo E with the stage frame.

These agreements hold for arbitrary candidate counts and submission lists,
without acceptance, freshness, ciphertext-shape or decryption-success premises.
They are expression agreement, not a claim that malformed elections decrypt.
`source_final_staticEq` then transfers all public observations between swapped
source output frames using B8. It retains freshness, valid ground candidates,
public submission recipes, and sequential acceptance after the honest board.

The source oracle is Figure 3's substitution/communication rule, Figure 4's
expressions and the explicit results definition in the
[author preprint](https://publications.bensmyth.com/files/Smyth12-attacking-Helios.pdf).
Figure 6's abbreviated final output repeats the last tally index; the model
follows Figure 4's corresponding candidate index. The control below makes this
choice observable. No new cryptographic equation or tuple-guard change is added.

## Controls and evidence

[Ten kernel controls](../../ExplainableCrypto/Helios/Symbolic/SourcePayloadSPOT.lean)
cover old-variable noncapture, correct nesting of two input binders, private
renaming, disjoint public/private indices, E-rewriting under input, exact first
partial binding, semantic rejection of a wrong candidate's ciphertext, the
actual nonliteral zero/one candidate results, and a nonempty election with tally
two. The three directed mutants are also retained as checked Boolean failures.
The wrong-candidate semantic control uses full-E no-match and normal-shape
inversion, independently of the raw comparator.

The [experiment](../../ExplainableCrypto/Helios/Symbolic/SourcePayloadExperiments.lean)
uses exact syntactic equality for substitution laws. Its payload fixture oracle
uses raw normalization plus numeric summaries on directed inputs; it does not
decide arbitrary E equality. Three defects fail at input zero: capture of an
old variable, changing a public handle during private flattening, and repeating
the last candidate's tally. Seeds 1, 7 and 42 each pass 500 cases at size 40,
with zero gave-up cases. A 2048-input backstop covers nested bodies and locals,
one/two candidates, zero through four extra ballots and both swaps.

Targeted builds pass: input binding 1006 jobs; payload syntax 1007 (in the gate
log); agreement 1008; gate 1098; controls 1150.

Latest integrated verification: `lake build` passes **3776 jobs**, with
**2494** nonempty standard-only and **24** axiom-free reports. The claim audit
covers **1532** public theorem entries and **77** current-status documents.
All seven changed Lean sources have current oleans; **977** local
links resolve. No proof holes, custom axioms, warnings or errors were found;
`git diff --check` passes. Log: `tmp/variable-overlap/source-payload-full-build.log`.
The increment adds 32 public theorem audits, including ten kernel controls,
and eight definition checks. The targeted controls pass 1150 jobs.

## Next source-correspondence obligation

Use the checked term-binder operations to define the source input continuations
and residual process syntax. The next proof must connect private communications
and public output/input labels to the stage transitions under structural
rules and restriction, including fresh output-name/handle renaming. The actual
trustee payloads now have proved agreement; they should not become an assumed
premise of that correspondence. Once every source transition is covered, lift
stage matching to weak labelled bisimilarity and the complete secrecy theorem.

See the [process stages](helios-process-stages.md),
[blueprint](helios-proof-blueprint.md), [results ledger](helios-results.md),
and [sole task list](../../task%20list.md).
