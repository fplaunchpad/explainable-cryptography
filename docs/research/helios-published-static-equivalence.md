# Published transcript static equivalence

B8 is complete. `Historical.General.accepted_final_staticEq` proves static
equivalence of the actual five-handle final frames for fresh names, arbitrary
valid ground candidate substitutions, and every public submission sequence
accepted after the two honest ballots. It has no remaining static-equivalence,
minimum-transport, observation or trustee-binding callback premise. The four-
handle partial frame and equivalent individual-handle frame are also covered.
B9 process matching and B10 labelled bisimilarity remain open; this theorem
alone is not the full symbolic ballot-secrecy theorem.

## The argument

`Term.TrusteeFree secret` inspects every term position. At each partial-decryption
node it requires the key to be unequal under full E to the designated secret.
This semantic key guard is needed because reducing a key expression can expose
the secret name. `TrusteeFreeValue` asks for an E-equal representative satisfying
the predicate; raw result expressions can contain partials that disappear when
decryption succeeds.

The predicate is invariant under E0 and preserved forward by all seven oriented
rules in every context. Confluence then excludes a trustee-free representative
of an actual secret-keyed partial. Literal-bit initial frames satisfy the
predicate; initial name non-deducibility excludes public construction of a
secret-keyed partial. Transport to arbitrary valid candidate representatives
proves `initial_recipe_trustee_free` for every public initial recipe.

Value reflection retains all arguments of public keys, pairs, encryption and
proof constructors, partial-decryption constructors, addition and composition.
For multiplication, the existing normal-factor/fusion theorems show that only
outer E7 fusion remains after normalizing the children. E7 retains every
component, so `TrusteeFreeValue.mul_iff` reflects the invariant to both factors.
No new homomorphic equation or cryptographic implementation is introduced.

`expanded_minimum_trustee_free_support` proves exact old-plus-results syntax
for every minimum expanded recipe with a trustee-free value. Stuck destructors
retain their arguments. Whole minimum decryptions cannot succeed, and minimum
proof checks cannot return `ok`. Successful minimum projections have the
previously proved old-honest-handle form. Trustee-partial variables are excluded
by their non-free values. This induction requires numeric published results,
but not acceptance, freshness, or the source public-name policy.

Every initial tally recipe is public when its submissions are public. A minimum
recipe equal to that tally therefore has exact result-only syntax. The previous
shared numeral-realization theorem transfers its entire tally binding using
B7. Acceptance supplies shared numeric results. This discharges
`accepted_expanded_trustee_binding` in both directions and enters the already
checked local assembly, simultaneous minimum induction and presentation lifting.
All twelve local operator cases are closed.

## Formal artifact and assumptions

- [Invariant](../../ExplainableCrypto/Helios/Symbolic/TrusteeFreeSyntax.lean),
  [reduction](../../ExplainableCrypto/Helios/Symbolic/TrusteeFreeReduction.lean),
  [initial values](../../ExplainableCrypto/Helios/Symbolic/InitialTrusteeFree.lean).
- [Constructor/arithmetic reflection](../../ExplainableCrypto/Helios/Symbolic/TrusteeFreeValues.lean),
  [multiplication](../../ExplainableCrypto/Helios/Symbolic/TrusteeFreeMultiplication.lean),
  [stuck destructors](../../ExplainableCrypto/Helios/Symbolic/TrusteeFreeDestructors.lean).
- [Minimum support](../../ExplainableCrypto/Helios/Symbolic/TrusteeFreeMinimumSupport.lean)
  and [published static equivalence](../../ExplainableCrypto/Helios/Symbolic/PublishedStaticEquivalence.lean).

The final theorem uses the existing exact E/E0 signature, full restricted-name
policy, `Names.Fresh`, both valid ground candidate substitutions, public
`Recipe 3` submissions, and source `AcceptsSequence` after `honestBoardRecipes`.
The tuple-guard correction remains part of acceptance. Ordinary structured-key
E5 and whole-ciphertext E6 binding remain intact. Neither candidate equality nor
pointwise frame equality is assumed. Arbitrarily nested equality tests over
all actual published handles are quantified by `Frame.StaticEq`.

Submission recipes here use the retained initial handles. Connecting adaptive
process inputs to flattened recipes, matching acceptance/rejection and ordering,
and assembling labelled bisimilarity for the intended voter scope are B9/B10.

## Controls and evidence

[Ten kernel controls](../../ExplainableCrypto/Helios/Symbolic/TrusteeFreeSPOT.lean)
retain semantic key rejection, opaque-position and homomorphic erasure rejection,
erasable raw syntax, actual result values, nested public constructions, the
minimum-size premise, unequal nonliteral candidates, a nonempty accepted
sequence with tally two, and a ten-node minimum using a numeric result as nonce.
The negative support fixture has a free value but mentions a partial handle in
an erased argument; it is explicitly nonminimum. Numeric realization is never
assumed to preserve minimum size.

The [bounded experiment](../../ExplainableCrypto/Helios/Symbolic/TrusteeFreeExperiments.lean)
uses a fixture detector based on raw normalization of keys, not a decision
procedure for full E. All three known-defect campaigns fail at input zero:
ignoring opaque positions, testing only raw literal keys, and reflecting raw
syntax backwards through an erasing projection. Positive seeds 1, 7 and 42
run 500 cases each at size 40 with no gave-up cases; 2048 deterministic inputs
cover all seven rules, eight background equations, nested contexts, initial
frames in both swaps and bidirectional E7 component retention. Search success
is bounded evidence; the general claims above are kernel proofs.

Targeted builds: invariant 995 jobs; reduction 996; initial 997; constructor
reflection 998; multiplication 999; destructors 1000; minimum support 1001;
static-equivalence assembly 1002; gate 1112; controls 1140.

Latest integrated verification: `lake build` passes **3766 jobs**, with
**2437** nonempty standard-only and **21** axiom-free reports. The claim audit
covers **1472** public theorem entries and **75** current-status documents.
All twelve changed Lean sources have current oleans; **946** local
links resolve. No proof holes, custom axioms, warnings or errors were found;
`git diff --check` passes. Log: `tmp/variable-overlap/trustee-free-full-build.log`.
The increment adds 48 public theorem audits, including ten kernel controls,
and three definition checks. The targeted controls pass 1140 jobs.

See the [maintained blueprint](helios-proof-blueprint.md),
[results ledger](helios-results.md), and [sole task list](../../task%20list.md).

[Historical process stages](helios-process-stages.md) now have checked
reachable-state invariants, same-label transition matching in both directions,
and static equivalence at every reached public domain. The twelve-stage model
allows arbitrary public input recipes, stops on rejection, and requires every
eligible input before publication. Ten controls include completed zero/two-input
elections, replay rejection and tally two. The next B9 obligation is operational
correspondence with the source applied-pi processes, including substitutions,
private messages, structural rules and fresh binders. B9/B10 remain open;
coverage stays 8/10 (80%, unweighted).


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
