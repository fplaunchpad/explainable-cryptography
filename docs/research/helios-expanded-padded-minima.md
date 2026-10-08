# Padded payload minima and complete expanded multiplication transport

Current status (2026-09-11): [B8 is complete](helios-published-static-equivalence.md).
The full partial/final-frame static-equivalence theorems discharge the binding
and local-induction premises left open in this record's historical checkpoint.
B9 process matching and B10 labelled bisimilarity remain open.

Status: machine-checked, global padded minima and all local multiplication
cases under two-way smaller minima. Current milestone:
[B8](helios-proof-blueprint.md). The global shared-minimum induction and the
full symbolic secrecy theorem remain open.

## Price padded payloads with published numerals

[`PaddedNumericHandleCosts`](../../ExplainableCrypto/Helios/Symbolic/PaddedNumericHandleCosts.lean)
reuses the existing numeric-handle summary and least attainable numeric cost.
The padded cost, measured as syntax nodes plus one, is:

```text
max 2 (sum of atom occurrence costs
       + (if numeric total = 0 then 0 else least numeric-handle cost of total))
```

An atom occurrence contributes its node count plus one. Repeated atoms remain
repeated. A zero total needs no numeric contribution when atoms remain, but
the whole recipe always has at least one syntax node. A positive total can use
published numeral handles; its cost need not equal the literal-only cost.

Every raw recipe pays at least this padded cost. Every public skeleton attains
it with a public representative retaining the exact atom bag and numeric
total. Equal such data preserve zero-padded values under any substitution
satisfying the same numeric-handle table. This sound equality theorem requires
no semantic atom or destination-minimum premise. It asserts padded equality,
not raw E0 equality between recipes or equality without padding.

## Establish global padded minimum size

[`ExpandedPaddedMinima`](../../ExplainableCrypto/Helios/Symbolic/ExpandedPaddedMinima.lean)
uses full-E atom classification and minimum atom-cost bags to show that padded
equality preserves this cost. Replacing an arbitrary public competitor by a
global minimum brings it within that classification. A skeleton attaining
its cost is therefore globally minimum under padded equality, against all
public recipes over all expanded handles.

`expanded_padded_minimum_representative` supplies such a representative when
the original nonnumeric atoms are minimum. It preserves the exact atom bag
and numeric total and is no larger than the source. The theorem retains the
caller's public-name policy, actual frame, explicit numeric table and source
result equations. Acceptance supplies a single table valid in both assignments.

## Close the one-constructor mixed case

[`ExpandedSingleMixedTransport`](../../ExplainableCrypto/Helios/Symbolic/ExpandedSingleMixedTransport.lean)
first recovers minimum nonce/payload components from minimum multiplication
leaves in a one-constructor assembly. The grouped components are actual
components of that sole constructed leaf. A minimum nonce and a globally
padded-minimum payload give a global mixed minimum, because every competitor
retains the same honest indexed costs and padded payload equality.

The single-constructor transport theorem chooses a padded representative using
the shared accepted numeric table. Its padded value is preserved in both
worlds. Smaller observations supply destination ciphertext-valuedness through
the existing assembly/key theorem, permitting mixed grouping in both worlds.
This closes the general one-constructor case, including non-atomic payloads.

`accepted_expanded_minimum_children_mul_shared_of_two_way_minima` combines all
multiplication cases: an already-minimum parent, non-ciphertext products,
honest products, constructed-only products, and mixed products with one or
multiple constructors. Its public interface needs fresh names, public accepted
submissions, source-minimum children and the two strict smaller-minimum
hypotheses. No separate coherence, observation or successful-destructor premise
remains. Those two induction hypotheses still require the global simultaneous
proof; this local theorem does not establish final-frame static equivalence.

## Controls and bounded refutation

The [cost gate](../../ExplainableCrypto/Helios/Symbolic/ExpandedPaddedExperiments.lean)
compares the candidate formula with independent exhaustive enumeration of
numeric-handle and literal multiplicities, including an optional literal zero.
It detects literal-only positive costs, free empty all-zero payloads and a
greedy choice at input zero, seed 1, zero shrinks. Seeds 1, 7 and 42 each pass
500 cases at size 40 with `gaveUp=0`. All 4096 deterministic inputs pass, covering
zero through five denominations, zero through nine totals and zero through
three atoms of costs two through four. These are addition-skeleton checks for
synthetic numeric tables, not full-E equality decisions or protocol executions.

Eight [kernel controls](../../ExplainableCrypto/Helios/Symbolic/ExpandedPaddedSPOT.lean)
establish a one-node global padded representative for a payload containing
published zero, preserved in two different-vote worlds; nonempty zero payloads;
three-node duplicate-atom minima; a cheap actual published tally of two after
nonempty accepted submissions; rejection of unpadded zero deletion; the
non-greedy optimum for denominations three/four; the complete multiplication
interface on the formerly unresolved one-constructor input; and a nine-node
mixed minimum with a repeated, non-atomic padded payload.

The exact multiplication-interface control uses a reflexive destination to
inhabit both smaller-minimum premises without assuming B8. Other controls
establish actual different-vote padded preservation and nonempty publication.
The interface control's source is nonminimum despite minimum immediate
children, and the returned representative has exactly seven nodes.

## Remaining frontier

All expanded-frame multiplication local cases are checked under the two-way
smaller-minimum induction interface. Remaining local pair/selector and
successful-case transport must still feed that global induction. The expanded,
partial and final static-equivalence lifting theorems are already checked but
their common-minimum premises remain open. B8, B9 process matching and B10 full
symbolic secrecy are incomplete; coverage stays seven of ten milestones (70%
unweighted, not effort or time remaining). See the [results
ledger](helios-results.md) for integrated evidence.

Integrated verification: full `lake build` passes 3735 jobs, with nineteen new
public theorem audits and all eight kernel controls. The log contains 2299
nonempty reports using only `propext`, `Classical.choice` and `Quot.sound`, plus
21 axiom-free reports. The claim checker covers 1334 public theorem entries and
70 current-status documents. Log: `tmp/variable-overlap/expanded-padded-full-build.log`.

[Expanded pair/selector transport](helios-expanded-pair-selector-minima.md) now
closes those three local roots without smaller-test premises. All local roots
and the simultaneous induction are assembled conditionally: successful
decryption/checking transport in both directions is the remaining requirement
for expanded, partial and final static equivalence.

[Result-handle realization](helios-result-handle-binding.md) now transfers full
tally bindings for all public old-plus-results recipes, including nested uses,
without size or minimum hypotheses. Only minimum ciphertexts without a
result-only presentation remain in the trustee-binding callback. A checked
ten-node minimum result-nonce recipe refutes old-only syntax and grows to
fourteen nodes under numeral realization.
