# Expanded minimum value shapes and decryption

Status: machine-checked under smaller equality observations. Pair, ciphertext
and partial-decryption value classes are invariant across the vote swap for
source-minimum recipes over the actual expanded frames. Both assignments need
numeric result values; fresh names and accepted public submissions discharge
that condition. Destination minimum size is not assumed.

This closes the shape-reflection dependency in B8. It does not establish
aggregate-partial static equivalence or full secrecy. In particular, preserving
these three value classes does not establish that a stuck decryption cannot
become a numeric success. A separate result-handle probe now excludes that
case with an explicit additional observation allowance, sufficient for the
syntactic minimum-decryption equality branch.

## Theorems and strict observation budget

[ExpandedValueShapes.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedValueShapes.lean)
provides:

- `expanded_minimum_value_shape_reflection`: each of the three destination
  value classes implies the corresponding source value class. It assumes
  numeric result values in both assignments, source minimum size and
  `ObservationsBelow φ ψ r.nodeCount`.
- `expanded_minimum_value_shapes_swap`: combines reflection with the previously
  checked forward ciphertext transport and explicit passive-value origins to
  give three equivalences under the same hypotheses.
- `accepted_expanded_minimum_value_shapes_swap`: discharges both numeric
  premises from fresh names and sequentially accepted public submissions.
- `accepted_expanded_minimum_decryption_match_numeric`: any destination match
  of a source-minimum decryption under the same strict observation budget uses
  a borrowed partial handle, returns that handle's corresponding result, and
  is E-equal to a numeral. This classifies a remaining case; it does not assert
  that such a match exists or that every decryption stays stuck.

The swap parameters are arbitrary. Observations compare public recipes whose
combined node count is strictly less than the source recipe's node count.
There is no added observation allowance and no assumption of full expanded
static equivalence.

[FrameValueShapeReflection.lean](../../ExplainableCrypto/Helios/Symbolic/FrameValueShapeReflection.lean)
extracts the structural induction shared by the initial and expanded frames.
`Frame.minimum_value_shape_reflection_of_cases` exposes four frame-specific
premises: chain shapes, minimum pair origins, ciphertext-product reflection,
and absence of data-shaped outputs from destination matches of minimum source
decryptions. Its last premise allows numeric decryption success.
[MinimumValueShapes.lean](../../ExplainableCrypto/Helios/Symbolic/MinimumValueShapes.lean)
now instantiates this helper with the existing initial-frame cases, preserving
its public theorem statements.

## Why decryption does not block shape reflection

[ExpandedShapeTools.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedShapeTools.lean)
derives the actual-frame premises:

1. `expanded_projection_chain_shape_reflection` classifies honest tails,
   honest ciphertext fields and borrowed partial handles. Numeric result
   handles cannot introduce these constructor shapes.
2. `expanded_minimum_passive_values_forward` retains the pair and partial
   constructor/borrowed forms without observation hypotheses.
3. In a product, reflected children have source ciphertext syntax. Applying
   the existing key-witness transport in reverse supplies two strictly smaller
   public key recipes. Their destination keys agree under E, so a smaller
   observation supplies source agreement and the homomorphic rule combines
   the source ciphertexts.
4. `expanded_minimum_decryption_match_result_of_reflection` uses smaller public
   key probes to exclude destination E5 and constructed-partial E6 matches.
   These would imply a source match, contradicting source minimum size.
5. For the remaining borrowed-partial E6 case,
   `expanded_trustee_E6_output` uses the entire ciphertext binding to prove
   equality of the match output with the actual result expression of that slot.
   `numeric_not_data_shapes` excludes all three constructor value classes from
   any numeral. This closes the structural induction without assuming E6
   failure transport.

Full E, minimum recipe size, public-name policy, actual expanded frames and
accepted-election semantics remain the trusted definitions. The modeled E6
binding and the previously checked numeric tally theorem justify the result
case. No cryptographic equations or publication values change.

## Result-handle probes and decryption equality

[ExpandedDecryptionTransport.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedDecryptionTransport.lean)
closes the remaining syntactic decryption case with an explicit budget:

- `accepted_expanded_minimum_decryption_failure_with_result_probe` assumes
  observations below `decryption.nodeCount + 2`. The preceding classification
  makes any destination success equal to its one-node published result handle.
  The whole-decryption/result test has size `decryption.nodeCount + 1`, strictly
  below that bound. Transferring it contradicts source minimality.
- `accepted_expanded_minimum_decryption_equality_swap` compares two syntactic
  minimum decryptions under the ordinary sum-of-their-sizes budget. Each has
  at least three nodes, so that budget supplies both required failure probes.
  With failure established in both worlds, equality is equivalent to the two
  ordered argument equalities, whose comparisons are strictly smaller.

This does not claim failure transfer below the decryption's own size. Shape
reflection uses that smaller budget and needs only numeric output exclusion;
the equality branch uses its larger combined budget. Exact source origins for
arbitrary recipes with stuck-decryption values are now checked in the
[expanded stuck-value record](helios-expanded-stuck-values.md).

## Independent controls and executable gate

[ExpandedShapeSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedShapeSPOT.lean)
retains eight controls: all expanded handle classes through the accepted theorem;
a minimum honest ciphertext selector; exclusion of data shapes from the
nonliteral numeral two; an actual public E5 decryption that returns a pair and
is nonminimum; an actual delayed E6 execution tied to the published result and
independently equal to one; and wrong-candidate rejection alongside both
correct-candidate successes; an exact negative/positive probe-budget check;
and an actual published E6 probe with a one-node result alias, proving that
probe nonminimum. The E5 control excludes the false claim that all
decryptions must have numeric outputs. The E6 control retains the full binding.

[ExpandedShapeExperiments.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedShapeExperiments.lean)
first detects both mutations at input 0, seed 1, zero shrinks. Seeds 1, 7 and 42
each pass 500 cases at size 40 with `gaveUp=0`; 2048 deterministic inputs pass.
The generator covers both candidates and assignments, zero through four
projection wrappers, and E5 outputs of all three data shapes. Expected E6
numbers come from the independent nonliteral candidate fixture. This gate
checks that semantic distinction on concrete executions; it does not test
universal minimality or prove full-E shape reflection. Raw normalization is
not a full-E decision procedure.

## Verification and remaining obligations

The gate passes 1019 jobs. The shared structural helper and refactored initial
proof pass 846 jobs. Expanded shape tools pass 933 jobs and the simultaneous
reflection target passes 935 jobs. Result-probe transport passes 936 jobs and
all eight controls pass 1041 jobs. Integrated checks and exact audit counts
are recorded in the [results ledger](helios-results.md).

The syntactic minimum-decryption equality branch is checked under its usual
combined-size observation premise. [Expanded stuck values](helios-expanded-stuck-values.md)
now supply arbitrary source origins, source minimum closure and both stuck-value
equality branches. Failure at the recipe-only budget is not claimed.
[Expanded composition](helios-expanded-composition.md) now supplies composition
origins, equality and minimum closure. [Expanded addition](helios-expanded-addition.md)
now closes its conditional equality branch using numeric-handle summaries.
[Addition minima](helios-expanded-addition-minima.md) now close addition shared
minimum transport. Multiplication shared minimum transport, remaining
shared minima and global B8 induction remain open. The [blueprint](helios-proof-blueprint.md) remains at B8,
seven of ten completed milestones (70% unweighted). Historical process matching
and full symbolic secrecy remain open at B9 and B10.

[Expanded public decryption](helios-expanded-public-decryption.md) now closes
direct E5 and constructed-partial E6. The remaining local case is complete
borrowed trustee tally-binding transfer for minimum ciphertexts. B7 handles
retained old recipes; general nested new-handle binding remains unproved.
