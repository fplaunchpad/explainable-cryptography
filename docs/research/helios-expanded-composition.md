# Expanded composition values and minimum size

Status: machine-checked under the stated numeric-result and smaller-observation
premises. The B8 composition-valued equality branch and composition minimum
closure now reuse the existing full-E factor bags and exact leaf-cost lemmas.
Repeated factors retain their multiplicity. No cryptographic equation changes.

## Actual composition origins

[CompositionOriginTools.lean](../../ExplainableCrypto/Helios/Symbolic/CompositionOriginTools.lean)
extracts `Frame.compose_form_of_paths`. This structural helper requires handle
exclusion, data-valued successful projections, and the absence of composition
values among matching decryption outputs. It does not require every decryption
to fail. The existing initial-frame origin proof now instantiates the helper
with its original no-match argument, preserving its two public theorem
statements in
[MinimumCompositionOrigins.lean](../../ExplainableCrypto/Helios/Symbolic/MinimumCompositionOrigins.lean).

[ExpandedCompositionOrigins.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedCompositionOrigins.lean)
provides the actual expanded-frame premises:

- `numeric_not_composition` excludes every numeral, including sums above one,
  from composition values under full E.
- `expanded_handle_not_composition` excludes old key/pair handles, new partial
  handles and numeric result handles.
- `expanded_minimum_compose_form` derives exact composition syntax from a
  source composition value. It retains an arbitrary caller public-name policy
  and assumes numeric results in that source assignment.
- `accepted_expanded_minimum_compose_form_after_swap` derives the same syntax
  from a destination composition value, using source minimum size and
  observations strictly below that recipe's size. Accepted public submissions
  and fresh names discharge numeric results in both assignments.

For the after-swap projection case, smaller pair-shape reflection supplies a
source pair argument and the existing successful-minimum-projection theorem
supplies honest data in the destination. For decryption, the checked match
classification permits a borrowed E6 success whose output is numeric; that
output cannot be a composition. The proof does not assume failure transfer at
the recipe-only budget or spend the larger result-probe allowance.

## Factor equality and minimum closure

[ExpandedCompositionTransport.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedCompositionTransport.lean)
reuses the existing composition machinery:

1. `expanded_minimum_compose_leaves_atomic` derives semantic indivisibility of
   minimum raw leaves from the source origin theorem.
2. `expanded_minimum_of_compose_leaves` uses full-E equality of factor bags and
   `minimum_leaf_cost_bags_eq` to compare every minimum competitor's total cost.
3. `expanded_minimum_compose_of_children` supplies minimum closure for two
   minimum children, under the caller's policy and source numeric results.
4. `accepted_expanded_minimum_compose_leaf_values` proves that raw leaves have
   no composition values in either assignment. Each leaf is an actual minimum
   subterm; its size fits the parent observation bound.
5. `accepted_expanded_minimum_composition_equality_swap` reduces the two value
   comparisons to full-E class bags and applies the existing
   `composition_leaf_bag_transfer` to strictly smaller public leaf comparisons.

The last theorem covers arbitrary source-minimum recipes whose source values
are compositions, with arbitrary swap parameters and accepted public
submissions. Its observation bound is the sum of the two original recipe
sizes. Destination minimum size and global expanded static equivalence are
not assumed. The smaller-observation premise remains open globally.

The source composition law is associative and commutative, with no unit or
idempotence rule. Full E, publicness, recipe size, candidate substitutions,
expanded publication and accepted-election semantics remain the trusted model.
The original homomorphic law and factor accounting are reused unchanged.

## Controls and executable gate

[ExpandedCompositionSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedCompositionSPOT.lean)
retains eight controls: all actual handles are non-compositions; composition
of published minimum children is minimum; duplicated zero-result factors do
not collapse; reassociation and permutation instantiate the accepted equality
interface in a diagonal election; a projection leaf hides a composition and
is nonminimum; an actual published-partial-key E5 wrapper exposes a composition
and is nonminimum; actual E6 succeeds with the independently expected numeric
one and no composition value; and an arbitrary frame publishing a composition
at one handle defeats minimum constructor closure. The last control makes the
handle-exclusion premise necessary; it is not an attack on the actual election.

[ExpandedCompositionExperiments.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedCompositionExperiments.lean)
detects duplicate deletion and the hidden-composition mutation at input 0,
seed 1, zero shrinks. Seeds 1, 7 and 42 each pass 500 cases at size 40 with
`gaveUp=0`; 2048 deterministic inputs pass over both candidates and assignments,
partial/result/key/stuck leaves, repeated factors and successful E5 wrappers.
The expected factor lists preserve all three independently chosen occurrences.
The gate checks executable behavior on this family, not universal minimum size
or full-E equality. Raw normalization is not a full-E decision procedure.

## Verification and remaining scope

The gate passes 1023 jobs; the generic helper and initial-frame refactor pass
851 jobs; expanded origins pass 940 jobs; factor equality and minimum closure
pass 941 jobs. The [results ledger](helios-results.md) records final controls,
integrated build and type/axiom audit evidence. All eight controls pass 1051
jobs. Full `lake build` passes 3680 jobs, with 2069 nonempty standard-only axiom
reports, 20 axiom-free reports, 1103 public theorem entries and 59 current-status
documents. Eighteen new theorem audits include the eight controls. Log:
`tmp/variable-overlap/expanded-compose-full-build.log`.

[Expanded addition](helios-expanded-addition.md) now closes its conditional
equality branch, including numeric result handles, and
[addition minima](helios-expanded-addition-minima.md) now close its shared minimum
transport. The [ciphertext assembly theorem](helios-expanded-ciphertext-assemblies.md)
now closes conditional ciphertext equality. B8 still needs multiplication
shared minimum transport, remaining shared minima, successful-case integration
and global observation induction.
The [blueprint](helios-proof-blueprint.md) remains at seven of ten completed
milestones (70% unweighted), with B9 historical process matching and B10 full
symbolic secrecy open.
