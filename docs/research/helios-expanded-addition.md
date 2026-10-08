# Addition equality with published numeric handles

Status: machine-checked, conditional equality branch. Current milestone:
[B8](helios-proof-blueprint.md). The public statement
[`accepted_expanded_minimum_addition_equality_swap`](../../ExplainableCrypto/Helios/Symbolic/ExpandedAdditionTransport.lean)
transfers full-E equality between two source-minimum addition-valued recipes
in actual accepted expanded frames. It derives the shared tally numbers and
both worlds' semantic atom conditions. Its remaining premise is agreement on
strictly smaller public recipe comparisons.

## Statement and assumptions

For fresh names, arbitrary valid ground candidates, public submissions accepted
in sequence, and any two swap assignments, let `φ` and `ψ` be their expanded
frames. If `r` and `s` are public minimum recipes for `φ`, both have addition
E-values in `φ`, and `φ.ObservationsBelow ψ (r.nodeCount+s.nodeCount)`, then:

```text
EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s).
```

The observation bound is a mathematical recipe-size bound. It means every
assumed comparison has total syntax size strictly below the original pair.
It is unrelated to tokens, money or execution time. Destination minimality and
full-frame static equivalence are not premises. Closing the simultaneous
observation/shared-minimum induction remains necessary to discharge the
smaller-observation premise globally.

## Published numbers change the addition summary

A published result is a one-node recipe even when its tally exceeds one.
The original addition/zero/one origin form and literal-only numeric costs do
not describe this case. The checked origin form now also includes result-slot
handles. Old key/ballot handles and partial slots cannot have additive values.
The initial-frame proof reuses the shared structural origin helper while
retaining its original public statements.

[`NumericHandleAddition`](../../ExplainableCrypto/Helios/Symbolic/NumericHandleAddition.lean)
adds a summary that expands known numeric handles along the outer addition
skeleton. It preserves all other recipe leaves, including duplicates. The
numeric field uses `Option Nat`: `none` and `some 0` remain distinct. A published
zero therefore cannot become a global additive identity.

The actual raw result is a decryption term, so the proof constructs an
E-equivalent value with literal numeral leaves before applying the existing
full-E addition-summary theorem. It proves the required equivalence from the
actual accepted tally equalities. It does not assume raw normalization decides
E or that a raw result decryption is a semantic nonnumeric atom.

## Why the size argument is well founded

A source-minimum decryption cannot succeed. Destination E6 success needs a
stronger argument because a borrowed partial can return a numeric result.
[`accepted_expanded_minimum_add_form_after_swap`](../../ExplainableCrypto/Helios/Symbolic/ExpandedAdditionOrigins.lean)
uses observations below `r.nodeCount+2`, which includes the comparison between
`r` and its one-node published-result alias. This comparison would contradict
source minimality if destination decryption succeeded.

For the equality branch, every nonnumeric summary leaf is strictly smaller
than its additive parent. The other recipe has at least one node, so
`leaf.nodeCount+2 ≤ r.nodeCount+s.nodeCount`. This pays for the destination
origin proof within the original induction bound. Pairwise atom equality tests
are also strictly smaller. The existing multiset-transfer theorem preserves
atom multiplicity; accepted common tally numbers preserve the numeric field.

## Controls and verification

[`ExpandedAdditionSPOT`](../../ExplainableCrypto/Helios/Symbolic/ExpandedAdditionSPOT.lean)
contains ten kernel controls: successful zero/result equality, failing equality
between distinct result slots, mixed additive minimum representatives, an
accepted one-node result of two, numeric-handle expansion, present zero,
repeated numbers and atoms, failure of naive minimum closure, successful
projection/E5 wrappers that are nonminimum, and successful numeric E6.

[`ExpandedAdditionExperiments`](../../ExplainableCrypto/Helios/Symbolic/ExpandedAdditionExperiments.lean)
checks both swap assignments and candidate slots, zero through four repeated
numeric occurrences, repeated name atoms and projection wrappers. Three
mutations treat a numeric handle as an atom, erase present zero or apply the
literal numeric cost bound to an accepted size-one result of two. The original
gate found all three at input zero with seed 1 and no shrinking, then passed
seeds 1, 7 and 42 (500 cases each, size 40, `gaveUp=0`) and 2048 deterministic
inputs. The integrated gate also compares the new handle-aware summary with
the independently prescribed numeric count and atom occurrences.

The targeted equality proof passes `lake build` (945 jobs). The final gate
passes 1044 jobs with all three mutations detected, three seeds passing without
`gaveUp`, and all 2048 deterministic inputs passing. Full `lake build` passes
3687 jobs, including all ten kernel controls and unchanged initial-frame callers.
Twenty-four new theorem audits and four definition checks cover the increment.
The integrated log has 2093 nonempty standard-only axiom reports, 20 axiom-free
reports, and claim coverage for 1127 public theorem entries and 60 current-status
documents. Log: `tmp/variable-overlap/expanded-add-full-build.log`. See the
[results ledger](helios-results.md).

## Remaining obligations

[Addition minimum representatives](helios-expanded-addition-minima.md) now
account for cheap published numerals and give shared minimum transport.
The checked zero-result plus one-result example has minimum children but a
nonminimum sum. The initial literal-only numeric cost argument cannot be
reused unchanged; the general minimum-closure claim is refuted in this scope.

Multiplication shared minimum transport, remaining shared minimum transport,
successful-case integration and the global expanded-frame induction remain
open. B9 process matching and B10 full secrecy remain open. This branch neither
proves final-frame static equivalence nor establishes protocol privacy from
equal tallies.
