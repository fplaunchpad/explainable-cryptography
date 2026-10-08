# Open voter and election application

Status: machine-checked. A single open source election instantiates to the
checked scoped initial election for arbitrary valid ground candidates. The
instantiation certificate includes the actual administration restrictions,
interleaved voter nonce scopes, local active definitions and exported public-key
variable. Every certified result has the existing initial source structural
path and action interfaces. One common fresh name allocation works for both
swapped worlds and every finite administration size/channel allocation.

This discharges the open-parameter application interface for the initial
source election. It does not establish the remaining later-process
correspondence or the final weak labelled bisimulation/secrecy theorem.

## Substitution and source certificates

[SourceProgramSubstitution.lean](../../ExplainableCrypto/Helios/Symbolic/SourceProgramSubstitution.lean)
provides variable substitution for term and scoped programs, with identity,
composition, value, let-count, scope-list and erasure laws. These are exact
syntactic identities. Name binders stay literal, so `ScopedTermProgram.FreshFor`
is a separate prerequisite for capture-avoiding source application.

[SourceNamedInstantiation.lean](../../ExplainableCrypto/Helios/Symbolic/SourceNamedInstantiation.lean)
extends the existing `Extended.Instantiates` graph through actual Named syntax.
Its active domains must map to variables; variable binders lift the substitution;
each name binder must avoid every supplied term's full literal name support.
`Instantiates.unique` proves exact result uniqueness. `compile_instantiates`
certifies compilation/application agreement under the freshness premise.
The graph is not a new structural or action rule. It does not promise
well-formedness for arbitrary substitutions; election well-formedness is proved
separately using its canonical source correspondence.

[SourceVoterSubstitution.lean](../../ExplainableCrypto/Helios/Symbolic/SourceVoterSubstitution.lean)
proves that register updates, saved ciphertext/proof references, the four
aggregate lets and the complete candidate sequence commute with substitution.
Each variable binder uses a lifted environment, including in full proof fields.

## One open voter template

[SourceOpenVoterTemplate.lean](../../ExplainableCrypto/Helios/Symbolic/SourceOpenVoterTemplate.lean)
uses `None` for the public-key parameter and `Some j` for each vote parameter.
Local term definitions introduce further Option layers. `voterTemplate_apply`
is literal equality to the checked ground scoped voter, retaining every let,
name scope and proof argument. `voterTemplate_instantiates` certifies the actual
compiled source application; `applied_voter_normalizes` reaches the complete
ballot output under the voter's nonce prefix.

## Whole-election application

[SourceElectionParameters.lean](../../ExplainableCrypto/Helios/Symbolic/SourceElectionParameters.lean)
keeps the public-key export and the two vote families in distinct summands.
The administration supplies its public-key term to each voter template. Candidate
application maps the key domain to the same exported variable and maps only
the vote families to the corresponding world's full ground terms.
`ElectionParametersFresh` checks all private base names, including secret and
auxiliary names; nonce freshness alone does not protect the outer scopes.

[SourceOpenElectionApplication.lean](../../ExplainableCrypto/Helios/Symbolic/SourceOpenElectionApplication.lean)
constructs `openElectionTemplate` independently of the supplied candidate vectors.
`openElectionTemplate_instantiates` certifies its exact scoped source instance,
including the key active frame and every outer restriction. The board/trustee
contain no vote parameters and remain unchanged under this substitution.
`instantiatedElection_normalizes` accepts any result with that exact source
certificate and derives its complete initial structural path.
`exists_open_election_application` allocates fresh names for arbitrary valid
ground candidates without changing their full terms.

[SourceAppliedElectionActions.lean](../../ExplainableCrypto/Helios/Symbolic/SourceAppliedElectionActions.lean)
retains arbitrary exact targets and labels in reduction/free/bound iff theorems.
It proves frame presentation, well-formedness, the full initial static witness
for two instances of the same open template, and an actual first private
communication. The certificates tie both instances to their respective candidate
substitutions; independently supplied unrelated processes do not satisfy the
public theorem's premise.

## Controls and verification

[SourceVoterApplicationSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SourceVoterApplicationSPOT.lean)
retains 23 public kernel controls. Literal expected values distinguish the key
from the first vote and verify the complete two-candidate ballot and all eight
lets. A supplied free `None` is shifted past the fresh local provider's domain
and remains free after application. Full fourth proof fields are retained.

Name-capturing graph instances and ground replacement of active domains are
rejected. These are failures of the exact freshness-guarded graph, not claims
that alpha-freshening can never enable application. A valid candidate with the
secret-key name in an E-discarded subterm passes nonce freshness but fails the
whole-policy condition. Fresh allocation supports arbitrary full valid terms.
Whole-election graph, normalization, well-formedness, full static witnesses and
actual private communication are checked.

The reality oracle is Cortier–Smyth Figure 4's public-key/vote parameters,
Definition 4's candidate substitutions and the source binder/active-substitution
rules. The proofs use exact syntax and existing full E. General substitution
proofs and directed kernel controls discharge this increment; there is no new
randomized cryptographic campaign or inference of secrecy from search failure.

Integrated verification at this open-application checkpoint: `lake build` passes **3959 jobs**. The log reports
**3738** nonempty standard-only and **68** axiom-free results. The claim audit
covers **2820** public theorem entries and **108** current-status documents.
All ten changed Lean sources have current oleans; **1340** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **69** theorem audits,
including **23** public kernel controls, and checks fifteen construction,
substitution and instantiation definitions.
Build log: `tmp/variable-overlap/source-voter-application-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-voter-application-verification.txt`.

Remaining obligations: general Named source correspondence, including fresh/injective assignment selection through arbitrary Named action
paths; remaining admissibility/action matching and final weak labelled
bisimilarity/symbolic secrecy. B9/B10 remain open at eight of ten unweighted
milestones. Maintain the [blueprint](helios-proof-blueprint.md),
[results](helios-results.md) and existing [task list](../../task%20list.md) item.

The subsequent [guarded board proof](helios-source-guarded-board.md) checks the
complete board construction, substitution and source activation, and compiled
full-E congruence. General Named operational correspondence remains open.

[Independent frame compatibility](helios-source-frame-compatibility.md) now
proves common-policy presentation compatibility and Named.StaticEq transitivity.
Fresh/injective assignment selection and general action matching remain open.

[Full Named body interpretation](helios-source-named-body.md) now proves
all-rule structural invariance and canonical/prenex full frame/body interpretation
under one assignment of both name sorts. That assignment may collide;
fresh/injective witness selection through arbitrary action paths and operational
correspondence remain open.
