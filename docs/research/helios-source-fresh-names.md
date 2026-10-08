# Fresh bound-name representatives

B9 now constructs legal alpha-equivalent representatives whose bound names
avoid any finite label-name set. For two actual states, it chooses one common
fresh policy and the same base/channel permutations, preserving full public-frame
static equivalence. A known source input keeps its original recipe, public
channel and target; that recipe is public under the fresh policy. These are
machine-checked supporting results. The full operational converse and secrecy
theorem remain open; B9/B10 stay at 8/10 unweighted milestones (80%).

## Finite freshness and nested binders

[SourceBoundNames.lean](../../ExplainableCrypto/Helios/Symbolic/SourceBoundNames.lean)
records `Named.boundNames` separately from free names and complete `allNames`.
A concrete fresh index is one above every index in a finite avoidance set, in
either name sort. Its two freshness theorems supply witnesses without a new
freshness axiom. Bound-name support maps under name permutations and stays
unchanged under typed variable renaming. A swap cannot change inner binders when
both swapped names are absent from their bound-name support.

[SourceFreshRepresentatives.lean](../../ExplainableCrypto/Helios/Symbolic/SourceFreshRepresentatives.lean)
proves `exists_fresh_boundNames` by structural induction on the current Named
syntax. At an outer name binder, the body is first freshened away from both the
forbidden set and the old outer binder. The new binder is then chosen outside
the body's complete support and the forbidden set. The resulting alpha swap
cannot capture or move an inner binder. Both base and channel sorts are covered,
as are parallel components and intervening variable restrictions.

Free-label freshness uses the complete label support, including all input
proof fields. Known free and bound-output actions transfer to the fresh source
representative with exactly the same label and target through the existing
Struct rule. This does not normalize that action's derivation or target.

## Coherent freshening of both worlds

[SourceFreshPrefixTools.lean](../../ExplainableCrypto/Helios/Symbolic/SourceFreshPrefixTools.lean)
provides name-map composition, restriction-list transport and the freshness
facts needed to keep inner prefix binders fixed during each outer swap.

[SourceCommonFreshPrefix.lean](../../ExplainableCrypto/Helios/Symbolic/SourceCommonFreshPrefix.lean)
proves `exists_common_fresh_prefix` for two bodies under the same finite name
prefix. Each new name avoids both bodies and the label-name set. Both resulting
bodies use the same base permutation and the same channel permutation. The new
prefix avoids the forbidden set, has distinct binders and keeps its length.
Every old binder's permuted name belongs to the new prefix. Names in the
forbidden set that were not originally bound are fixed by the permutation.
The result even handles repeated original binders, retaining the corresponding
possibly unused restrictions rather than dropping syntax.

[SourceFreshPolicy.lean](../../ExplainableCrypto/Helios/Symbolic/SourceFreshPolicy.lean)
connects those witnesses to actual canonical policies. For an original prefix
with distinct binders, injectivity, length and membership prove that the new
binder set is exactly the image of the old one. Its ordering is converted to
the canonical finite-set enumeration using source New-C. Consequently
`exists_common_fresh_policy` produces the exact image base-name and hidden-channel
policies for both bodies, not merely an unrelated fresh list.

## Actual input states and observations

[SourceFreshInputStates.lean](../../ExplainableCrypto/Helios/Symbolic/SourceFreshInputStates.lean)
applies common policy freshening to the complete active-frame/process states.
`exists_common_fresh_input_states` keeps the input recipe unchanged and makes
it public under the fresh policy. A public input channel is fixed. Both states
are structurally equivalent to their consistently renamed canonical forms, and
their full frames remain statically equivalent over all public recipes.

`input_action_common_fresh_states` additionally transfers an arbitrary known
named input to that fresh source, retaining the exact label and raw target.
Its public-channel premise is discharged by the previously proved channel
converse. The public-recipe condition is proved for the fresh policy, resolving
the representational issue exposed by the retained alpha-input counterexample.
The original fixed-policy assertion remains false and is not reinstated.

## Controls and remaining work

[SourceFreshNamesSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SourceFreshNamesSPOT.lean)
has eleven kernel controls. They check a concrete fresh index, occupied-name
rejection, bound versus free support, the complete fourth proof-field avoidance,
nested mixed name/variable binders and typed variable renaming. A repeated
prefix can become distinct without changing length. An old literal input keeps
its syntax while the private key actually moves and retains its pk constructor
at the old handle; an originally public literal stays fixed. The earlier alpha
counterexample retains its exact label/target at a fresh representative. Both
actual reached election worlds freshen coherently for arbitrary input recipes,
using the completed B7/B8 observation theorem.

No structural or operational rule was added or weakened for these results.
They use structural kernel proofs and independent controls, with no new
randomized cryptographic campaign or full privacy inference. The remaining
converse must recover full evaluated payload/continuation behavior and canonical
targets from arbitrary named structural/alpha derivations. Named-frame
observations/admissibility and outer voter nonce/let construction must still be
connected before weak labelled bisimilarity and symbolic secrecy. General
replication, mobile channels and name creation under arbitrary plain prefixes
are outside the current historical syntax.

The subsequent [active-variable interpretation](helios-source-interpretation.md)
now recovers evaluated internal behavior through all Extended structural paths
and preserves complete canonical frame values. The
[visible interpretation](helios-source-visible-interpretation.md) now also covers
every current Extended free/bound action with complete captured environments.
Named alpha/target interpretation remains the next correspondence obligation.

See the [blueprint](helios-proof-blueprint.md),
[channel closure and alpha-input boundary](helios-source-channel-closure.md),
[name restrictions](helios-source-name-restrictions.md) and
[renamed observations](helios-source-renamed-observations.md).

Integrated verification for the fresh-name checkpoint: `lake build` passes **3859 jobs**, with
**3036** nonempty standard-only and **48** axiom-free reports. The claim audit
covers **2098** public theorem entries and **92** current-status documents.
All nine changed Lean sources have current oleans; **1134** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-fresh-names-full-build.log`.
This increment adds 41 theorem audits, including eleven kernel controls, and
three definition checks. Targeted controls pass 1236 jobs. Freshness/hole/link
evidence: `tmp/variable-overlap/source-fresh-names-verification.txt`.
