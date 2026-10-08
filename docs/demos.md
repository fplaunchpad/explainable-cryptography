# Lean mutation-testing demonstrations

The `ExplainableCrypto/` directory contains literate, executable introductions to mutation coverage
for specifications. They do not require the research proposal to understand.

Set up the pinned Lean and Mathlib dependencies, then build all demonstrations from the
repository root:

```sh
lake exe cache get
lake build ExplainableCrypto
```

## Elementary model

The motivating problem is that proving a program against a specification does
not prove that the specification captures its author's intent. Mutation testing
makes nearby mistakes explicit and asks whether checked examples expose them.

The intended toy specification accepts functions `f : Nat → Nat` whose output
is never smaller than their input. The unmutated construction increments its
input.

The demo applies mutations at two layers:

1. **Definition mutants** change what acceptance means. Lean proves that one is
   weaker, one is stronger, and one is equivalent to the intended definition.
   Concrete functions separate the non-equivalent definitions.
2. **Construction mutants** change the function while keeping the intended
   definition fixed. Concrete inputs kill the `zero` and `decrement` mutants;
   the `identity` mutant is proved to preserve the chosen specification.

The final `#eval` commands print an explicit coverage inventory. Coverage is
measured over the chosen mutants, not over all possible natural-number inputs.
It is manual bookkeeping backed by the preceding theorems, not yet an automated
mutant generator or proof searcher. An unresolved mutant would remain in the
report rather than being treated as secure merely because no attack was found.

## One-time pad

[`ExplainableCrypto/OneTimePad/MutationTesting.lean`](../ExplainableCrypto/OneTimePad/MutationTesting.lean) applies the same method to a genuine
cryptographic definition. It uses Mathlib probability mass functions to:

1. define correctness and the row-equality form of perfect secrecy;
2. prove that an `n`-bit one-time pad meets both requirements;
3. separate definition mutants that retain only correctness or only secrecy;
4. kill cleartext and constant-output construction mutants; and
5. exhibit a checked two-bit witness showing why reusing a pad leaks
   information.

The file keeps probability infrastructure in Mathlib while leaving the cipher,
security definitions, mutants, and attacks visible in the demonstration.

### Visual attacks

Open [`ExplainableCrypto/OneTimePad/Visuals.lean`](../ExplainableCrypto/OneTimePad/Visuals.lean) in VS Code and place the cursor on either `#html`
command at the bottom. The Lean InfoView displays:

- the cleartext attack as a one-bit message/ciphertext probability table; and
- the reused-pad attack as two ciphertext-pair grids, with the checked
  distinguishing cells highlighted.

The widget computes finite key counts. The theorem
`uniform_probability_eq_count` connects those executable counts to the PMF
probabilities in the perfect-secrecy definition, so the display and proof use
the same semantics.

## Helios replay experiments

`ExplainableCrypto/Helios/` contains a finite symbolic model, checked replay and permutation
counterexamples, fresh-ballot and rejection controls, and Plausible campaigns.
See the [claim ledger](research/helios-results.md) for declarations, commands and
assumptions. Component weeding blocks the selected witnesses; general ballot
secrecy remains open. The entry point imports every Helios module.

The [symbolic layer](research/helios-symbolic.md) adds arbitrary recipe terms
and equational observations. Its [tuple-termination correction](research/helios-symbolic-tuple-guard.md)
is documented and has positive and negative controls.
