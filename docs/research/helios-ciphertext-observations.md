# Ciphertext equality as an observation induction step

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: machine-checked. The complete grouped equality matrix and recursive
key-coherence proof close the ciphertext-valued minimum-recipe branch under an
explicit induction hypothesis on smaller public equality tests. The hypothesis
is still unproved for arbitrary recipes. Full static equivalence, final frames
and ballot secrecy remain open.

The result builds on [arbitrary product grouping](helios-ciphertext-grouping.md)
and [mixed equality](helios-mixed-ciphertexts.md). It covers all positive candidate
counts and valid ground candidate substitutions, including abstention and
reducible representations, with `Names.Fresh` and the full name restriction in
the final induction theorem.

## All grouped comparisons

[GroupedCiphertextEquality.lean](../../ExplainableCrypto/Helios/Symbolic/GroupedCiphertextEquality.lean)
defines `CiphertextGroup.Observation` and proves its exact correspondence with
nonce/message equality. Let C denote a constructed-only group, H an honest-only
group and M a mixed group. For ciphertexts with semantic keys K and L:

| Left/right case | Equality criterion |
| --- | --- |
| C / C | K =E L, public nonce equality and public payload equality |
| H / H | K =E L and equal honest occurrence multisets |
| M / M | K =E L, equal honest multisets, public nonce equality and zero-padded public payload equality |
| C / H, H / C | false |
| C / M, M / C | false |
| H / M, M / H | false |

`CiphertextGroup.components_eq_iff` checks the component matrix under nonce-public
remainders and fresh honest labels. `ciphertext_eq_iff` adds the exact key
comparison. The publicness premise also retains the payloads for the later
public-observation argument; the separation reasoning concerns nonce remainders.

The new `mixed_nonce_not_honest` proves the H/M separation. Normalize an E-equal
protected representative of the public remainder. Its outer composition-factor
bag is nonempty and excludes every honest restricted literal. Full-E equality
to an honest-only combination would place one of those factors in an all-honest
bag, a contradiction. The lemma needs protection and restricted honest names;
it does not require name injectivity. It introduces no unit or raw-safety
premise. Ciphertext and proof atoms containing hidden nonces remain permissible
public remainder factors.

C/H and C/M separation follows from nonce-factor non-deducibility. Within M/M,
the honest occurrence bag fixes the common numeric message contribution within
a world. Zero-padding retains that contribution's presence while removing its
value from the equality comparison. C/C uses the unpadded payloads because no
honest numeric contribution is present.

## Key coherence is itself observable

[CiphertextObservationInduction.lean](../../ExplainableCrypto/Helios/Symbolic/CiphertextObservationInduction.lean)
defines `CiphertextAssembly.Coherent φ`. Leaves are coherent. At a multiplication
node, both children must be coherent and their selected key recipes must have
E-equal values in φ. The two key recipes come from disjoint subtrees.

`coherent_iff_ciphertext_value` proves that this predicate is exactly the
existence of a full-E ciphertext value for the assembly in the actual general
frame. The forward direction reconstructs a grouped ciphertext under the
selected key; the reverse direction uses full-E inversion to derive leaf key
agreement. Coherence is not a syntactic same-key test or an extra cryptographic
assumption.

`coherent_transfer` proves that coherence transfers whenever smaller public
key equality tests transfer. The proof uses the two child key-recipe bounds
against their disjoint child sizes. It does not compare the value of one key
recipe across worlds. Such values can change while the relevant pairwise
key-equality observations remain invariant.

## The precise induction interface

`Frame.ObservationsBelow φ ψ B` means: for every pair of public recipes r and s
whose node counts sum to less than B, equality of their evaluated values under
full E holds in φ exactly when it holds in ψ. This is a named premise, not a
proved all-recipe static-equivalence statement.

`CiphertextGroup.observation_transfer` uses the original assembly budgets to
bound the observations in the matrix. Constructed payloads are compared directly;
mixed payloads are padded by zero. Each pair has total size strictly smaller
than the original pair's total size. Key coherence uses the same measure.

`CiphertextAssembly.equality_swap_of_smaller` combines these facts for arbitrary
public assemblies that are coherent in the first world. It derives their
coherence in the second world from smaller observations, reconstructs both
grouped ciphertext values, and transfers the key and component comparisons.
It assumes neither second-world coherence nor pointwise equality of keys.

The final theorem `Historical.General.minimum_ciphertext_equality_swap` has
these premises:

- fresh names and arbitrary valid ground candidate substitutions;
- two minimum recipes under the full restriction in the unswapped frame;
- a supplied ciphertext value for each recipe in that frame;
- `ObservationsBelow` between unswapped and swapped frames, at the sum of the
  two original recipe node counts.

Its conclusion transfers equality of those same recipes between worlds. The
minimum-origin theorem derives both assemblies, and ciphertext inversion
derives coherence. No caller assembly certificate, coherence assumption,
second-world value, normality premise or preserved-minimality assumption is
required. This closes a branch of the intended induction; proving its smaller-
observation premise globally still requires the other cases and reduction
argument.

## Claim ledger and controls

Names below are in `ExplainableCrypto.Helios.Symbolic`; `General` abbreviates
`Historical.General`.

| Claim | Evidence | Declaration | Scope |
| --- | --- | --- | --- |
| A protected mixed nonce cannot equal an honest-only nonce | machine-checked | `mixed_nonce_not_honest` | Protected E-value, nonempty combinations and restricted labels |
| All nine group cases have exact component criteria | machine-checked | `General.CiphertextGroup.components_eq_iff` | Fresh names, nonce-public groups, actual candidate frames |
| Full ciphertext equality also retains key equality | machine-checked | `General.CiphertextGroup.ciphertext_eq_iff` | Arbitrary supplied semantic keys |
| Recursive coherence exactly characterizes ciphertext-valued assemblies | machine-checked | `General.CiphertextAssembly.coherent_iff_ciphertext_value` | Actual general frame and arbitrary assembly |
| Smaller key observations transfer coherence | machine-checked | `General.CiphertextAssembly.coherent_transfer` | Explicit smaller-observation premise and public assembly |
| Minimum ciphertext equality transfers from smaller tests | machine-checked | `General.minimum_ciphertext_equality_swap` | Both first-world minimum recipes have supplied ciphertext values; full restricted policy and freshness |

[CiphertextObservationSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/CiphertextObservationSPOT.lean)
contains seven checked controls. A literal three-group fixture checks all nine
comparisons in both actual vote worlds: three reflexive equalities and six
cross-case inequalities. Allowing a restricted literal as the public remainder
refutes mixed/honest separation, preserving the necessity of protection.

The wrapped-key assembly remains coherent with repeated honest factors; a
wrong-key public leaf is incoherent. Another public-only assembly uses an
honest ciphertext selector and a projection wrapper around it as its key
recipes. They agree within each world, so coherence holds in both worlds,
while the selected key value itself changes under the swap. This rules out
pointwise key preservation as an explanation.

The complete minimum-recipe theorem is instantiated using identical honest
candidate assignments in both frames and two unequal ciphertext values. This
makes the `ObservationsBelow` premise provable for every bound without assuming
the open different-vote theorem. Minimum existence preserves the two values,
and the checked nonce distinction rules out vacuous universal equality. This
diagonal control validates the interface's inhabitation, not different-vote
privacy.

## Executable scope and validation

`CiphertextObservationExperiments.lean` has two independent finite proxies.
The coherence gate compares a recursive tree predicate with equality of all
leaf key labels. Its mutation omits subtree key comparisons and fails at n=0,
seed 1, with zero shrinks.

The matrix gate compares literal public/honest nonce lists and exact payload
atom lists plus optional numeric counts. It checks the predicted criteria in
both scalar vote assignments, preserving the distinction between absent numeric
content and a present zero. The public nonce labels and honest labels are
disjoint by construction. This is a component-summary proxy, not evaluation
of arbitrary public recipes or a full-E decision procedure.

Both gates pass seeds 1, 7 and 42, each with 500 configured cases, maximum size
40 and `gaveUp=0`. A 256-input backstop passes, and 576 directed matrix inputs
cover all nine case pairs with 64 generated parameter settings each. Kernel
controls separately exercise actual general-frame values and wrong-key fusion.

Reproduce with:

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/CiphertextObservationExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
python3 scripts/check_helios_claims.py
```

The full build passes (3466 jobs), including 21 new public theorem type/axiom
audits and five definition checks. All 1172 nonempty axiom reports use only
`propext`, `Classical.choice` and `Quot.sound`; 17 additional reports are axiom-free.
There are no warnings, errors or `sorryAx`. The local log is
`tmp/variable-overlap/ciphertext-observation-full-build.log`. The source audit
checks 203 public theorem entries and selected stale claims in 13 current-status
documents; it does not replace elaboration or establish log freshness.

Trusted definitions remain E/E0, public recipes, nonce protection, general
candidate frames, assembly syntax and minimum node count. The reality oracle
is Cortier–Smyth Appendix B.3's ciphertext enrichment and E5–E7 key matching,
with the previously checked open-variable reflection defect accounted for.
No equation, public operation, custom axiom or confluence assumption changed.

The subsequent [proof-valued branch](helios-proof-observations.md) handles
constructed and honest proof equality under the same smaller-test premise.
Remaining work includes other value heads and the argument that arbitrary
recipe evaluations can be related across worlds. Choosing a
minimum representative in one world does not itself transport that replacement
to the other. Final partial-decryption frames and historical process matching
also remain open. The canonical [task list](../../task%20list.md) retains the
full static-equivalence objective.
