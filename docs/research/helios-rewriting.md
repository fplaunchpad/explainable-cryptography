# Structural rewriting for the historical theory

Status: termination, normal-form existence and raw root matching are
machine-checked. Confluence and the accepted-ballot characterisation remain open.

Goal: justify the reduction machinery invoked in Appendix B.2.2 of the
Cortier–Smyth author preprint (pp. 44–45). The paper orients E1, E2 and E5–E9
from left to right, modulo a background theory E0 containing AC for addition,
ciphertext multiplication and nonce composition, plus E3 and E4.

Candidate claim: the oriented reductions strictly decrease a natural-number
measure, including under any term context and before/after any E0 equality.
Consequently every term has a reachable irreducible term. The formal oracles
are `RewriteStep.weight_lt`, `ModuloStep.weight_lt`, `rewrite_wellFounded`
and `exists_normal_form` in `Symbolic/Rewriting.lean`.

Falsifier: one instantiated rule or contextual/background variant that fails
to decrease; an infinite reduction chain would refute termination. The independent
reality oracle is the printed rule list, with these hand-derived costs:
projection removes its projection and pairing nodes; decryption removes at
least its decryption/encryption nodes; E7 removes one encryption node and one
copy of the key; proof checking removes its check and proof nodes.

The proposed weight counts names/variables as one, constants as zero, unary
nodes as one, pair/partial/decryption nodes as one, ternary and proof nodes as
one. The three AC binary nodes contribute zero of their own. Child weights are
always added. Thus E3/E4 and AC preserve weight. Ordinary syntax-tree size
would not be invariant under E3/E4, so it is retained as a negative control.

Before general proofs, run seeded Plausible checks over instantiated reductions
and background equations, including nested contexts. Generate rule families by
construction instead of discarding arbitrary non-redexes. Test a false invariance
claim first. Testing supplies refutation evidence only; termination must follow
from a kernel-checked theorem for all terms and all contexts.

Residual obligations: confluence modulo E0, constructor analysis, nonce
non-deducibility, the ballot characterisation, static equivalence and process
matching remain open. Existence of an irreducible representative does not give
a unique representative, an equality decision procedure or a privacy theorem.

## Checked results

The trusted definitions are `BaseEquation`, its congruence closure `BaseEq`,
`RootStep`, `Context.fill`, `RewriteStep`, `ModuloStep` and `Term.cryptoWeight`.
`Equation.classify` checks that each generator of the existing E belongs to
one of the two parts. Both parts are proved sound in the existing E.

| Claim | Formal oracle | Scope |
| --- | --- | --- |
| Background equations preserve weight | `BaseEq.weight_eq` | All contexts, substitutions already instantiated as arbitrary terms, symmetry and transitivity |
| Oriented rules decrease weight | `RootStep.weight_lt`, `RewriteStep.weight_lt` | All seven schemata, all term argument positions |
| Reduction modulo E0 decreases weight | `ModuloStep.weight_lt` | Arbitrary E0 changes before and after the contextual reduction |
| No infinite sequence of oriented reductions modulo E0 | `rewrite_wellFounded` | Reverse orientation for Lean's well-founded-relation convention |
| Every term has an equivalent reachable irreducible term | `exists_equivalent_normal_form` | Classical existence, not an implemented selection algorithm or uniqueness theorem |
| Executable raw root matching is sound and complete | `rootReduce_sound`, `rootReduce_complete` | Syntactic root instances only; no context descent or E0 matching |
| Successful matcher outputs preserve E and decrease weight | `rootReduce_correct` | Statement refers to the actual returned term |

The root matcher returns a term paired with a `RootStep` proof. Its certificate
is erased for executable comparisons, and a separate soundness theorem connects
that ordinary output to the relation. No successful search is trusted without
that connection.

## Refutation gate and controls

The measure campaigns ran before the general termination proof. The negative
control, seed 1, refuted tree-size invariance at `n = 0` (`3 ≠ 1`, zero shrinks).
`tree_size_not_base_invariant` retains the failure as a kernel-checked result.

Three positive properties use seeds 1, 7 and 42, each configured for 500
instances and maximum generator size 40. All nine runs succeed with `gaveUp=0`:

- every member of the seven-rule fixture list decreases contextual weight;
- every member of the eight-equation E0 fixture list preserves contextual weight;
- the certified matcher returns the independently supplied right-hand side for
  every member of the seven-rule fixture list.

The first six runs precede the general proof; the last three validate the
subsequently implemented matcher. `generatedTerm` constructs raw terms at
depths 0–3, including variables, names, arithmetic, encryption, proof and
destructor nodes. `wrap` supplies directed nested contexts. The tests use no
premise filters, and their distribution is not claimed to cover every context
or election. General kernel proofs supply that coverage for the stated
weight properties. All seven root rule families and all eight background
fixtures are tested on every generated input.

Deterministic controls prove that constants are irreducible, a projection
actually reduces, the matcher recognises a right-key decryption and refuses
a wrong-key one. `nested_still_reduces` and `background_still_reduces`, paired
with their `*_root_no_match` results, prove that a failed root match is not
an irreducibility certificate. These are deliberate limits of the matcher,
not counterexamples to the termination theorem.

## Reproduction and remaining work

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/RewriteExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
```

The shared [Plausible harness](../../ExplainableCrypto/Testing/Plausible.lean)
inspects outcomes and fails evaluation on `gaveUp`, unexpected failures or a
missed negative control. Both the earlier finite experiments and the new
rewriting campaigns use it.

The next proof obligation is confluence modulo E0, or an alternative complete
structural analysis sufficient for the nonce and ballot lemmas. Termination
alone cannot establish constructor injectivity, indistinguishability or ballot
secrecy. No normal-form decision procedure, convergence theorem or privacy
result is claimed here.

Validation: the full `lake build` passes (3283 jobs), with no warnings or errors.
The axiom audit reports only subsets of `propext`, `Classical.choice` and
`Quot.sound`; no new custom axioms or proof holes are reported.
