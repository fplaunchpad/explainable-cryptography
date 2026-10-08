# Non-ciphertext multiplication shared minima

Status: machine-checked, conditional local shared-minimum transport.
Current milestone: [B8](helios-proof-blueprint.md).
[`accepted_expanded_minimum_children_non_ciphertext_mul_shared`](../../ExplainableCrypto/Helios/Symbolic/ExpandedMulMinimumClosure.lean)
proves the expanded non-ciphertext multiplication case: minimum children and
shared minima of strictly smaller public recipes yield a shared globally
minimum representative of their product.

## Exact statement and remaining premise

The accepted-election wrapper assumes fresh names, valid ground candidates,
public sequentially accepted submissions, and source-minimum child recipes.
The whole product must have no ciphertext value in the source frame. For each
strictly smaller public recipe, the induction premise supplies a representative
that is minimum in the source and preserves evaluation in both frames.

The conclusion supplies the same guarantee for the product itself. It does
not assume the original product is minimum. Only forward smaller shared minima
are needed; there is no smaller-observation or reverse-transport premise for
this branch. A lower-level theorem accepts source numeric-result origins and
an arbitrary destination frame over the same handles.

## Reused proof and global minimum size

Minimum raw leaves have single-factor normal representatives. Expanded numeric
origins exclude a hidden normal product beneath a non-multiplication leaf.
The existing normalization/partition theorem then retains every source
occurrence, including ciphertext factors that fuse into one group.

A normal partition with minimum piece recipes certifies global minimum size.
The proof chooses a globally minimum public competitor, constructs its normal
partition, matches all normal factor occurrences and compares their exact
piece costs. It bounds every public competitor, not only regroupings of the
original product. The caller's public-name policy remains explicit in these
one-world minimum theorems.

The generic comparison is extracted in
[`minimum_of_normal_partition_of_competitors`](../../ExplainableCrypto/Helios/Symbolic/MultiplicationMinimumPartitions.lean).
The shared reassembly proof is extracted in
[`Frame.sharedMinimum_of_partition_shared_pieces_of_competitors`](../../ExplainableCrypto/Helios/Symbolic/MultiplicationSharedReassembly.lean).
Both initial and expanded frames now call these shared arguments. The original
initial-frame public statements are unchanged. Existing E3 fusion, factor
partitions, occurrence costs and piece reassembly remain the algebraic core.

For a non-ciphertext parent, the normal endpoint remains a product. Each of its
partition pieces has a strictly smaller public recipe. The induction premise
supplies their shared minima; existing reassembly preserves destination
values, and the source partition theorem establishes global minimality.
Destination normality and destination minimum size are unnecessary.

## Evidence and scope

The [gate](../../ExplainableCrypto/Helios/Symbolic/ExpandedMulMinimumExperiments.lean)
detects source-only replacement, duplicate-cost deletion and use of unfused
target factors at input zero, seed 1, zero shrinks. Seeds 1, 7 and 42 each pass
500 cases at size 40 with `gaveUp=0`; all 2048 deterministic inputs pass. Each
uses two through eight pieces, both swaps, actual partial/result handles,
duplicates, delayed recipes and fused public ciphertext groups. Comparisons use
raw normalization and the existing nonce/numeric summaries on these fixtures,
not a complete E decision procedure or a general minimum-size algorithm.

Eight [kernel controls](../../ExplainableCrypto/Helios/Symbolic/ExpandedMulMinimumSPOT.lean)
cover a four-to-one-node published-result wrapper; two wrapped zero-result
occurrences shrinking from nine to exactly three nodes without dropping a
factor; actual published-child normal partitions; minimum ciphertext fusion;
a product of minimum children shrinking from eleven to at most eight nodes;
a source-only replacement counterexample; strict public piece bounds with at
least two pieces; and a nonminimum leaf hiding a product. The full local
shrinking control uses diagonal candidates to inhabit its smaller-minimum
premise. The published-result reassembly controls use different votes in both
assignments.

The generic refactor passes 893 jobs; expanded minimum closure passes 944 jobs;
the gate passes 1052 jobs and all eight controls pass 1076 jobs. Seventeen new
public theorem audits cover this increment. Integrated evidence is recorded
in the [results ledger](helios-results.md).

## Remaining frontier

[Constructed-only ciphertext products](helios-expanded-constructed-minima.md)
now have shared minima under the two smaller-minimum hypotheses; ciphertext
constructor minimum closure is checked as well. Mixed products,
remaining local/selector and successful-case transport must still feed the
two-way shared-minimum induction. The checked
[observation lifting](helios-expanded-observation-assembly.md) converts those
premises into the actual final-frame target once they are proved. B8 final-frame
equivalence, B9 process matching and B10 full symbolic secrecy remain open;
coverage stays seven of ten milestones (70% unweighted, not effort remaining).


Integrated verification: full `lake build` passes 3716 jobs, including seventeen
new theorem audits and all eight kernel controls. The log contains 2220 nonempty
reports using only `propext`, `Classical.choice` and `Quot.sound`, plus 20
axiom-free reports. The claim checker covers 1254 public theorem entries and
66 current-status documents. Log:
`tmp/variable-overlap/expanded-mul-min-full-build.log`.

Honest-only combinations now have [global expanded-frame minima](helios-expanded-honest-minima.md)
and need no smaller premises for shared transport. Exact indexed occurrences
exclude honest groups from nonminimum ciphertext products with minimum children.

[Expanded mixed compression](helios-expanded-mixed-compression.md) now closes
mixed products with at least two public constructors under two-way smaller
minima. Minimum mixed competitors have exactly one constructor and preserve
honest indices, public nonce equality and zero-padded payload equality. The
remaining mixed case needs global padded payload minima with published numeric
handle costs.

[Expanded padded minima](helios-expanded-padded-minima.md) now close the general
one-constructor mixed case using published numeric-handle costs and shared
padded values. All multiplication local cases are assembled under the two
smaller-minimum hypotheses. Remaining pair/selector and successful-case
transport and the global simultaneous induction stay open.
