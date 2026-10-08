# Interleaved voter nonce scopes

Status: machine-checked. The actual initial election with each voter nonce
restriction immediately before its ciphertext/proof lets has a source structural
path to the existing allocated-name initial election. The path includes both
voters, the finite board and trustee, the public-key frame, the auxiliary base
name and the complete private-channel policy. It applies to every positive
candidate count and every finite number of additional voters.

The theorem requires `Names.Fresh` and absence of allocated nonces from the
full ground candidate terms. A common allocation satisfying those conditions
exists for every pair of ground parameter vectors, including nonliteral
representatives. The allocation leaves those vectors unchanged. Thus the
freshness premise is not a restriction to literal bit syntax.

## Scope-aware computation

[SourceScopedTermProgram.lean](../../ExplainableCrypto/Helios/Symbolic/SourceScopedTermProgram.lean)
adds a construction language with result, term-let and name-scope nodes.
`compile` uses the existing `Named` constructors. `Hoistable` requires every
later restricted name to be absent from the current provider's full term.
`compile_hoist` moves the actual name scopes to a prefix by New-Par/New-C;
`compile_normalizes` then eliminates the local term definitions. The erased
program retains every term let and the complete output value.

[SourceVoterNonceScopes.lean](../../ExplainableCrypto/Helios/Symbolic/SourceVoterNonceScopes.lean)
builds Figure 4's interleaved structure, followed by the four aggregate lets.
The proof-register fourth field is the new ciphertext variable, and the
name-support lemmas track exactly which literal names its provider contains.
`scopedVoterProgram_normalizes` retains precisely that voter's nonce prefix
around the complete historical ballot output. `NoncesFreshFor` examines every
literal name in each candidate term, including discarded subterms.

## Fresh allocation and the administration

[SourceFreshElectionAllocation.lean](../../ExplainableCrypto/Helios/Symbolic/SourceFreshElectionAllocation.lean)
constructs distinct names above a supplied bound. `exists_fresh_election_names`
avoids any finite set; `exists_parameter_fresh_election` includes the full name
support of both parameter vectors. One allocation supports both swapped worlds.

[SourceVoterScopeContext.lean](../../ExplainableCrypto/Helios/Symbolic/SourceVoterScopeContext.lean)
proves that one voter's full ballot contains no nonce from the other voter,
under the stated freshness premises. It moves both voter prefixes across an
explicit administration context whose free names avoid them.
[SourceAdministrationNameSupport.lean](../../ExplainableCrypto/Helios/Symbolic/SourceAdministrationNameSupport.lean)
discharges that condition for the actual board and trustee, for all candidate
and voter counts. `Agent.BasePublic` is a syntactic base-name condition over
all payloads and guards; it is not a secrecy predicate or attacker model.

## Complete initial source path

[SourceNamePrefixPolicies.lean](../../ExplainableCrypto/Helios/Symbolic/SourceNamePrefixPolicies.lean)
normalizes restriction prefixes with the same exact name set. Duplicate
occurrences are removed by existing unused-name rules, and order changes use
New-C. It does not remove a name merely because it is private or add a name
without a premise.

[SourceScopedVoterElection.lean](../../ExplainableCrypto/Helios/Symbolic/SourceScopedVoterElection.lean)
places only administration base names and private channels at the outer level;
the voters introduce their own nonces inside their computations. The public-key
frame is retained. `administration_nonce_policy` proves the exact combined
policy, and `scopedVoterElection_normalizes` supplies the full source path to
`Named.restrictedState` of `sourceState ... .start`.

[SourceScopedElectionActions.lean](../../ExplainableCrypto/Helios/Symbolic/SourceScopedElectionActions.lean)
transfers exact-target reduction/free/bound action interfaces, frame
presentation, well-formedness and initial static equivalence. The actual first
private communication is derived. `exists_scoped_election_correspondence`
supplies one fresh allocation for arbitrary valid ground candidates and all
finite administration sizes/channels, with both initial source paths and the
full initial static witness. This is not the final weak labelled bisimulation.

## Controls and evidence

[SourceVoterScopeSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SourceVoterScopeSPOT.lean)
retains 25 public kernel controls. The independent literal trace fixes both
nonce positions and all eight term lets for two candidates; the complete ballot
output retains both nonce restrictions. A candidate term E-equal to zero still
contains a discarded nonce and fails the syntactic hoisting criterion. A fresh
allocation admits that unchanged term. These controls refute an omitted
freshness premise; they do not prove that every alternative structural path is
impossible when the criterion fails.

Further controls cover the full fourth proof field, variables beneath a name
scope, both voters beside the real administration, whole-election source
normalization, static witnesses, well-formedness and actual private communication.
Duplicate prefix normalization succeeds; deleting a used channel restriction
fails by the existing channel invariant.

General structural/name-support proofs and directed kernel controls discharge
this increment. No new randomized cryptographic campaign or search-based
security claim is made. Full E and all source structural/action rules are
unchanged. Reality oracle: Cortier–Smyth Figures 2–4, particularly interleaved
voter nonce restrictions and New-Par's freshness condition.

Integrated verification at this voter-scope checkpoint: `lake build` passes **3951 jobs**. The log reports
**3673** nonempty standard-only and **64** axiom-free results. The claim audit
covers **2751** public theorem entries and **107** current-status documents.
All eleven changed Lean sources have current oleans; **1325** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **75** theorem audits,
including **25** public kernel controls, and checks nineteen construction,
freshness and compilation definitions. Targeted controls pass **1160 jobs**.
Build log: `tmp/variable-overlap/source-voter-scopes-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-voter-scopes-verification.txt`.

Remaining source obligations include general Named correspondence, canonical
environment/body correspondence and remaining admissibility/action matching.
The final weak labelled bisimilarity and symbolic secrecy theorem remain open.
B9/B10 stay incomplete at eight of ten unweighted milestones. Maintain the
[blueprint](helios-proof-blueprint.md), [results ledger](helios-results.md) and
existing [task list](../../task%20list.md) item.

The subsequent [open-application increment](helios-source-voter-application.md)
certifies whole-election candidate substitution under every name/variable scope.
It preserves the actual public-key domain and supplies fresh allocation for the
stronger complete private-policy freshness condition.

The later [guarded board construction](helios-source-guarded-board.md) retains
its explicit lets and proves source activation and compiled congruence, while
leaving general Named correspondence open.

[Independent frame compatibility](helios-source-frame-compatibility.md) now
proves common-policy presentation compatibility and Named.StaticEq transitivity.
Fresh/injective assignment selection and general action matching remain open.

[Full Named body interpretation](helios-source-named-body.md) now proves
all-rule structural invariance and canonical/prenex full frame/body interpretation
under one assignment of both name sorts. That assignment may collide;
fresh/injective witness selection through arbitrary action paths and operational
correspondence remain open.
