# Minimum multiplication partitions

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: **machine-checked supporting results for B7-M**. A partition with a
fully normal endpoint and globally minimum source pieces certifies minimum
size of the whole recipe. This closes the source cost comparison, including
products of two normal groups. Arbitrary multiplication shared transport
remains conjectured.

## Compare exact piece costs

`MultiplicationPartition.minimum_pieces_cost_le` compares two public recipe
partitions with full-E-equal evaluated values and irreducible endpoints.
Confluence makes the endpoints E0-equal, so their final factor bags match with
every occurrence retained. Each minimum piece in the first partition costs no
more than its equal-valued public counterpart in the second. Summing these
inequalities and using both exact budgets bounds the whole first recipe by the
second. The second partition's pieces need not be minimum.

This comparison is generic over the substitution and public-name policy.
Endpoint normality is necessary: ciphertext fusion changes the number and
values of outer factors even when the individual factors are normal.

## Derive source partitions and global minimality

`MinimalRecipe.mul_leaf` transfers minimum size through raw product contexts.
`minimum_mul_leaf_normal_forms_source` uses initial-frame minimum origins to
derive single-factor normal representatives for minimum raw leaves. Ciphertext
leaves are allowed. The result covers either assignment, valid ground candidate
substitutions and any caller name policy, without a freshness or smaller-test
premise.

`normal_partition_of_minimum_mul_leaves` retains the raw leaf recipes while
normalizing and fusing their evaluated factors. It provides a normal endpoint
and exact partition even when the whole source recipe is not minimum. This
existence theorem does not establish minimum size of fused groups.

`minimum_of_normal_partition` compares the supplied partition with an arbitrary
minimum equivalent's derived normal partition. The generic cost inequality
then proves global source minimality. The initial historical frame is essential
to deriving the competitor partition from minimum origins.

`MultiplicationPartition.single` represents one normal factor with an arbitrary
source recipe, including a product that evaluates to a fused ciphertext.
`minimum_mul_of_normal_groups` combines two such pieces: if their source
recipes are minimum and their single-factor representatives form an irreducible
product, the whole source product is minimum. Its syntax is consequently a
shared representative in any destination frame using the same policy.

## Controls and remaining work

Seven SPOTs check repeated two-node key pieces with a five-node product minimum,
a ciphertext group beside a key with a seven-node minimum, nine-to-six-node
fusion despite minimum children, normal-partition existence without source
minimality, a nonminimum piece with a normal endpoint, failure after directly
publishing a product, and a five-versus-eight-node comparison whose competitor
piece contains a removable wrapper. The fusion control explicitly distinguishes
a normal-factor family from an irreducible whole endpoint.

The pre-proof gate detects omission of a duplicate cost and use of an unfused
factor bag at input 0, seed 1, zero shrinks. Seeds 1, 7 and 42 pass 500 configured
cases each, size 40, gaveUp=0; all 2048 deterministic inputs pass. The generator
retains repeated non-atomic pieces, removable wrappers, labelled ciphertext
fusion groups, exact budgets and both assignments. This is refutation evidence,
not a secrecy proof. Log: `tmp/variable-overlap/multiplication-minimum-gate.log`.

Full build and public type/axiom evidence appear in the
[results ledger](helios-results.md#multiplication-partition-minimum-result).
The [blueprint](helios-proof-blueprint.md) remains at B7-M with nine of twelve
operator cases closed. The subsequent
[shared-piece reassembly](helios-multiplication-reassembly.md) now constructs
that representative and discharges non-ciphertext products by well-founded
recipe induction. Arbitrary whole-ciphertext products still need a shared
minimum construction; normal partitions alone do not supply it. Successful decryption/checking, final-frame equivalence,
process matching and symbolic ballot secrecy also remain open.
