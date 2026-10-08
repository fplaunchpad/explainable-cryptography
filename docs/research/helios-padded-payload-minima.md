# Zero-padded payload minima and multiplication closure

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: **machine-checked**. B7-M is complete within the unbounded simultaneous
recipe induction. All multiplication classes have shared source-minimum
representatives under its strict smaller-minimum hypotheses. The remaining
operator cases are successful decryption and successful proof checking.
The [blueprint](helios-proof-blueprint.md) moves to B7-C, successful proof
checking, with **ten of twelve operators** closed. **Six of ten top-level
milestones** remain closed; initial-frame static equivalence is still unproved.

## Padded minimum cost

[PaddedPayloadCosts.lean](../../ExplainableCrypto/Helios/Symbolic/PaddedPayloadCosts.lean)
retains every nonnumeric atom and every one in the outer addition skeleton.
Appending zero makes numeric absence and a present zero agree. The minimum
payload node-count-plus-one is

```text
max 2 (sum of (atom.nodeCount + 1) over all atom occurrences + 2 * oneCount).
```

The lower bound of two supplies a real one-node zero recipe for an all-zero
payload. It does not introduce an empty term or a global zero identity.
`public_padded_minimum_cost_representative` constructs a public representative
attaining that cost, preserves the exact atom bag and proves raw E0 equality
after appending zero. Its unpadded values need not be equal.

[PaddedPayloadMinima.lean](../../ExplainableCrypto/Helios/Symbolic/PaddedPayloadMinima.lean)
defines `PaddedMinimalRecipe` as least size among all public recipes equal after
zero padding in the specified source frame. This is a minimization relation,
not a change to E/E0. Such a recipe is also an ordinary source minimum.

`minimum_padded_summary_cost_eq` uses the existing minimum-atom classification
and complete addition-value summaries to equate atom cost bags and one counts.
`padded_minimum_of_exact_cost` compares with **any** public padded-equal recipe:
first take that competitor's ordinary minimum, whose atoms are minimum, then
apply cost equality and the universal raw-cost bound.
`padded_minimum_representative` therefore supplies a globally padded-minimum
representative for any outer addition skeleton with source-minimum atoms.
It preserves raw padded E0 equality and does not increase size. The caller's
public-name restriction is preserved; no freshness or observation premise is
needed for these payload theorems.

## Closing the last mixed case

[SingleMixedMinimumClosure.lean](../../ExplainableCrypto/Helios/Symbolic/SingleMixedMinimumClosure.lean)
proves that a one-constructor assembly with minimum multiplication leaves has
minimum nonce and payload components. These are the actual constructor's
subrecipes, not components merely guessed from its evaluated value.

`minimum_mixed_of_minimum_components` compares against every minimum mixed
competitor. Nonce minimum size, padded payload minimum size and the fixed honest
indexed occurrence cost jointly establish global mixed minimum size.
`single_mixed_shared_of_smaller_observations` then minimizes the payload and
preserves both mixed values using raw padded equality. Its observation premise
is used only to transfer key coherence to the destination.

`minimum_children_mul_shared_of_two_way_minima` covers the full multiplication
operator. Non-ciphertext products use shared partition reassembly; honest-only
products are already minimum; constructed-only and multiple-constructor mixed
products strictly compress; one-constructor mixed products use padded minima.
The theorem assumes only minimum immediate children and shared minima for
strictly smaller recipes in both directions. The existing simultaneous
unbounded induction supplies those hypotheses. No successful-destructor
transport premise occurs in this operator theorem.

[DecryptCheckTransport.lean](../../ExplainableCrypto/Helios/Symbolic/DecryptCheckTransport.lean)
removes multiplication from the residual interface. The current sufficient
theorem is `Historical.General.staticEq_of_decrypt_check_transport`.
Its two `Frame.DecryptCheckTransport` premises still require successful `dec`
and successful `checkspk` transport in both directions, with both strict smaller
minimum hypotheses available. Initial-frame static equivalence, final public
transcript equivalence, process matching and top-level secrecy remain open.

## Controls and validation

[PaddedMinimumSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/PaddedMinimumSPOT.lean)
contains eight controls: duplicate four-node atoms give an eleven-to-nine-node
padded minimum without losing an occurrence; zero and two-one minimum cases;
refuted unpadded zero cancellation; a nonminimum wrapped-atom counterexample;
a twenty-four-to-twenty-two-node mixed shared minimum with non-atomic payload
and repeated higher-index honest selectors; failure without minimum leaves;
application of the full multiplication theorem to the previous minimum-child
zero-padding fixture; and a nonconstant diagonal reduced-criterion instance.

[PaddedMinimumExperiments.lean](../../ExplainableCrypto/Helios/Symbolic/PaddedMinimumExperiments.lean)
detects lost ones, lost non-atomic occurrences and mistaken unpadded cancellation
at input 0, seed 1, zero shrinks. Seeds 1, 7 and 42 each pass 500 configured
cases at size 40, gaveUp=0. All 2048 deterministic inputs pass, covering one
through seven leaves and both assignments. Independent leaf counts determine
the expected cost; a separate retained-leaf construction supplies the shortened
recipe. The test comparison is limited to the generated addition summaries,
not a full-E decision procedure or proof by bounded search.
Log: `tmp/variable-overlap/padded-minimum-gate.log`.

The [task list](../../task%20list.md) remains the sole development backlog.


Integrated verification: `lake build` succeeds with **3598 jobs**. Twenty-three
new public theorem type/axiom audits include eight SPOTs; four definitions are
checked. The full log reports **1710 nonempty standard-only axiom sets and 20
axiom-free reports**, without warnings, errors or `sorryAx`. The claim checker
covers **744 public theorem entries and 42 current-status documents**, and checks
that the blueprint's reported closed-operator count matches its operator table.
Log: `tmp/variable-overlap/padded-minimum-full-build.log`.

The [expanded padded minimum theorem](helios-expanded-padded-minima.md) now
uses least published-numeral costs in the corresponding frame. Its replacement
preserves padded values under the shared numeric table; it does not claim raw
E0 equality between unexpanded handle recipes. All expanded multiplication
local cases are assembled under the two smaller-minimum hypotheses.
