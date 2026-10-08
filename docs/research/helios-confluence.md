# Confluence modulo the background equations

Status: the conditional confluence framework and the three-ciphertext
overlap are machine-checked. Confluence of the whole Helios rewrite system
is still conjectured. Termination and raw root matching were checked earlier.

Goal: justify the use of unique normal forms modulo E0 in the historical
accepted-ballot and static-equivalence arguments. The candidate claim is that
any two reductions from the same term have descendants equal modulo E0.
Raw syntactic equality of endpoints is a deliberately false alternative:
a projection can return zero or an E0-equivalent `zero + zero`, both irreducible
under the oriented rules and syntactically distinct.

The formal oracle will separate a generic termination-plus-local-confluence
argument from protocol-specific overlap proofs. Proving the generic implication
does not establish its local-confluence premise for Helios.

The first directed source overlap has three ciphertexts under the same key.
Combining the first two then the third yields left-associated nonce/plaintext
combinations. Combining the last two first yields right-associated ones. AC in
E0 joins the results. The independent oracle is E7 with associativity of `*`,
`+` and nonce composition in §5.2.1 and Appendix B.2.2. No identity law is used.

Before proving that overlap for arbitrary terms, test the two routes with the
existing certified root matcher and an explicit one-associativity alignment of
the expected endpoints. Keep the false raw-equality test and all mismatch/failure
outcomes visible. This is a directed family, not enumeration of all critical
pairs or proof of their completeness.

Remaining obligations include all overlaps involving nonlinear proof/decryption
rules, background-equation interactions, and a theorem that the analysed cases
exhaust arbitrary competing reductions. The complete local-confluence premise
must not be introduced as a cryptographic axiom or a hidden assumption of the
final privacy theorem.

## Checked results and exact scope

All declarations are in `ExplainableCrypto.Helios.Symbolic`.

| Claim | Evidence | Remaining hypothesis or limit |
| --- | --- | --- |
| Reductions can be transported through all contexts and E0 representatives | `ModuloStep.context`, `ReducesModulo.context`, `ModuloStep.pre_base`, `ModuloStep.post_base` | Properties of the defined relations |
| Termination and local confluence imply confluence modulo E0 | `confluence_of_local_confluence` | Explicit `LocalConfluentModulo V` hypothesis; not proved for the whole theory |
| Irreducible descendants are unique modulo E0 | `normal_forms_unique_of_local_confluence` | Same explicit hypothesis |
| E-equality is equivalent to joinability | `eqE_iff_join_of_local_confluence` | Same explicit hypothesis; E itself is unchanged |
| E-equality of irreducible terms reduces to E0-equality | `irreducible_eqE_iff_base_of_local_confluence` | Local confluence and irreducibility are explicit hypotheses |
| The homomorphic three-ciphertext peak is reachable and joinable | `triple_peak_joined` | Unconditional, for arbitrary terms under one shared encryption key |
| Raw syntactic confluence is false for the modulo-step presentation | `raw_confluence_false` | Irreducible endpoints zero and zero+zero remain E0-equal |

`ReducesModulo` includes a final E0 equality even for zero oriented steps.
This permits two terminal representatives of the same background class to be
joined. The earlier `Reduces` relation is retained and embedded explicitly;
its zero-step case is literal identity. `JoinModulo.sound` connects joins back
to the original E-equality.

The three-ciphertext theorem proves actual reductions from a common ancestor
to both intermediate branches, then reductions to E0-equivalent endpoints.
It does not merely prove the two expressions equal in E. It covers one
homomorphic overlap family, not the completeness of a critical-pair analysis.

## Refutation gate

`ConfluenceExperiments.lean` runs the two combination orders through the certified
root matcher. A deliberately false equality of raw endpoints fails with seed 1,
`n=0`, zero shrinks; `triple_raw_endpoints_differ` retains that mismatch. The
stronger `raw_confluence_false` control proves why syntactic joining is the wrong
objective, rather than merely recording unequal intermediate expressions.

The positive campaign checks both successful reduction routes and their endpoint
alignment for seeds 1, 7 and 42, each configured for 500 instances and maximum
size 40. All three succeed with `gaveUp=0`. Inputs use the existing depth-0–3
term generator; no premises are filtered. The alignment function handles only
the known associativity pattern. It is not a background normaliser. The
parametric theorem `triple_endpoints_base` independently checks the necessary
E0 equivalence for arbitrary arguments.

The campaign ran before the parametric overlap proof. These results support
only that directed family. Nonlinear proof/decryption overlaps and exhaustive
case coverage are open in the canonical task list.

## Reproduction

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/ConfluenceExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
```

The audit checks all new public theorem types and prints their axioms. Conditional
results retain their hypotheses in these types; no local-confluence or privacy
axiom was added to make them unconditional.

Validation at handoff: `lake build` passes (3287 jobs). The audit reports only
subsets of `propext`, `Classical.choice` and `Quot.sound`, with no custom axioms
or `sorryAx`. No build warnings or errors were reported.
