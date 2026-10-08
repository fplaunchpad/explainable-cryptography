# Shared minima for addition

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: **machine-checked**. Addition with source-minimum children has a
source-minimum representative that is equal before substitution in E0. It
therefore preserves evaluation in every destination frame with the same public
policy. This closes blueprint B7-A; it does not prove initial-frame static
equivalence or ballot secrecy.

## Preserve numeric presence and occurrence costs

The raw addition summary retains a bag of nonnumeric recipe occurrences and an
optional numeric count. Absence has cost zero. A present zero has cost two;
a positive count `n` has cost `2*n`. These costs measure node count plus one.
Each nonnumeric occurrence contributes its own node count plus one.

`Term.addSyntaxSummary_cost_le` bounds the summary cost by the raw recipe cost.
`public_addition_minimum_cost_representative` realizes that bound with a public
term E0-equal to the original raw recipe. For a present zero it retains one zero;
for a positive count it retains exactly that many ones. There is no global zero
identity and no saturation of one plus one. Nonnumeric occurrences are retained.

## Prove global source minimality

`minimum_add_atoms_atomic` uses the initial-frame minimum-add origin theorem.
A minimum recipe with an additive value must be raw addition, zero or one.
Each nonnumeric raw leaf excludes all three shapes, so its value is a semantic
addition atom. This result accepts any caller name policy and either assignment;
it requires no freshness or observation-transfer premise.

`minimum_add_summary_cost_eq` compares recipes whose raw nonnumeric atoms are
source-minimum. Equality after substitution gives equal full-E class bags and
equal optional numeric counts. Equal-valued minimum leaves have equal costs,
so the raw summary costs agree, including every occurrence.

`minimum_add_of_exact_cost` compares a cost-attaining recipe with an arbitrary
minimum equivalent. The latter's atoms inherit minimum size from their contexts.
The equal-summary-cost theorem and raw cost bound show that the proposed recipe
is no larger. This proves global minimality, rather than minimality only among
addition rearrangements.

`minimum_add_representative` combines realization and global minimality.
`minimum_children_add_shared` applies it to minimum children in the actual
initial historical frame. The representative's raw E0 equality holds under
every substitution, so the destination may be any frame under the full source
policy. The source minimum theorem itself retains an arbitrary caller policy.

## Remaining interface

`Frame.DecryptCheckMulTransport` retains successful decryption, successful proof
checking and multiplication. `four_case_transport_of_three_cases` supplies
addition to the preceding interface. The checked
`Historical.General.staticEq_of_decrypt_check_mul_transport` still assumes the
three remaining cases in both orientations, alongside name freshness and valid
candidate substitutions. Neither different-vote premise has been proved.

## Independent controls and verification

The pre-proof gate detects arbitrary-zero deletion and one-plus-one saturation
at input 0, seed 1, with zero shrinks. Seeds 1, 7 and 42 pass 500 configured cases
each at size 40, gaveUp=0. All 2048 deterministic inputs pass, covering numeric
absence, present zero, repeated ones/atoms and both assignments. This checks raw
canonical summaries, costs and normalized public fixtures, not secrecy.
The log is `tmp/variable-overlap/addition-minimum-gate.log`.

Eight checked SPOTs retain numeric collapse with nonminimum parents, separated
numeric collapse to a three-node two-one minimum, observable zero and atom
duplicates, a thirteen-to-eleven-node reduction with repeated four-node atoms,
the minimum-atom premise, weaker policy with colliding nonces, failure after
directly publishing a sum, and a diagonal three-case criterion with distinct
public names. Literal expected costs and equation boundaries are independent
of the normalization experiment.

The integrated build and axiom evidence are recorded in the
[results ledger](helios-results.md#addition-shared-minimum-result).
The [blueprint](helios-proof-blueprint.md) records the current frontier.
