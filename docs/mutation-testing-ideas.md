# Ideas

This document collects possible extensions to the Lean demonstration.
It is exploratory background. Track active priorities and completion only in
[task list.md](../task%20list.md).

## Automatic, proof-producing mutation testing

The hand-written demonstration in [`ExplainableCrypto/MutationTesting.lean`](../ExplainableCrypto/MutationTesting.lean) could become an
automatic, proof-producing mutation testing system.

**Status:** Paused.

Automation separates into three problems:

1. Generate plausible mutants.
2. Find witnesses or proofs that classify them.
3. Have Lean check every reported result.

The third problem is straightforward: Lean's kernel checks the resulting proof
terms. Mutant generation and witness discovery are the substantive work.

### Feasibility in Lean

The complete pipeline for the current toy example can run inside Lean. Ordinary
Lean functions can generate mutations over typed syntax, interpret each mutant,
enumerate candidate constructions and inputs, and assemble proof-carrying
classification results. A custom elaborator command such as
`#mutate_spec intendedSpec` could invoke this pipeline and produce the report.

Lean metaprogramming provides syntax quotations and transformations, custom
commands, access to elaborated expressions and the declaration environment, and
custom tactics. The mutation and search code need not be trusted for logical
soundness: every successful classification must contain a proof term that
Lean's kernel checks. Bugs in the automation may miss mutants, leave results
unresolved, or produce poor mutations, but they cannot certify a false result.

Although metaprograms can inspect and transform arbitrary elaborated Lean
expressions, using that as the first implementation would be brittle. Dependent
types, inserted coercions, implicit arguments, and elaborator-generated terms
make it difficult to ensure that mutations remain meaningful. The recommended
architecture is therefore a small typed, domain-specific syntax with explicit
mutation operators. This makes eligible mutation locations visible and keeps
generated mutants type-correct by construction.

Mutation generation and kernel validation are consequently feasible entirely
within Lean. Witness and proof discovery will become the main difficulty when
the system scales from this finite toy domain to cryptographic games.

### Stage 1: Represent specifications as syntax

Do not begin by rewriting arbitrary elaborated Lean expressions. Define a small,
typed specification language whose semantics are explicit. For the current toy
example, it might begin as:

```lean
inductive Bound
  | zero
  | input
  | successorInput

structure SpecSyntax where
  lowerBound : Bound

def SpecSyntax.denote (s : SpecSyntax) : Spec := ...
```

This representation makes the eligible mutation locations explicit and stops a
mutation from producing an ill-typed specification. The existing `Intended`,
`Weaker`, and `Stronger` definitions should become denotations of syntax values.

### Stage 2: Generate depth-one mutants

Define a catalogue of mutation operators over the syntax:

```lean
def mutateBound : Bound → List Bound := ...
def generateMutants : SpecSyntax → List Mutant := ...
```

Each `Mutant` should record:

- the operator applied;
- the syntax-tree location changed;
- the original expression;
- the replacement expression; and
- the resulting syntax tree.

Depth one means applying one operator at one eligible location. Normalize the
generated syntax and remove syntactic duplicates before classification.

### Stage 3: Classify definition mutants

Maintain a finite catalogue of candidate schemes such as `zero`, `identity`,
`increment`, and `decrement`. For every mutant definition `M`, attempt to prove
both implication directions:

```lean
∀ f, Intended f → M f
∀ f, M f → Intended f
```

Also search the candidate catalogue for schemes satisfying:

```lean
Intended f ∧ ¬ M f
M f ∧ ¬ Intended f
```

The required certificates determine the classification:

- **Equivalent:** implication proofs in both directions.
- **Strictly weaker:** `Intended → M`, plus a scheme satisfying `M` but not
  `Intended`.
- **Strictly stronger:** `M → Intended`, plus a scheme satisfying `Intended` but
  not `M`.
- **Incomparable:** a separating scheme in each direction.
- **Unresolved:** the required certificates were not found.

A failed proof or witness search is never evidence for an implication,
equivalence, or security claim.

### Stage 4: Generate and test construction mutants

Represent constructions with a second small syntax tree. Generate depth-one
edits while keeping the intended specification fixed. Enumerate candidate inputs
and try to construct:

```lean
Attack mutant
```

If a checked attack is found, classify the mutant as killed. Otherwise, try to
prove that it still satisfies `Intended`. If neither proof is found, retain the
mutant as unresolved.

The finite toy model may use exhaustive input search. Any such result must state
whether it proves the unbounded property or only a bounded approximation.

### Stage 5: Make the report proof-carrying

Replace the demonstration's manually maintained status list with result types
that contain the required certificates:

```lean
inductive DefinitionResult
  | equivalent ...
  | strictlyWeaker ...
  | strictlyStronger ...
  | incomparable ...
  | unresolved

inductive ConstructionResult
  | killed (attack : Attack mutant)
  | preservesSpec (proof : Intended mutant)
  | unresolved
```

Generate the coverage report only from these values. Search code and mutation
generators remain outside the trusted base: a bug in them can miss results or
produce unhelpful mutants, but it cannot manufacture a false certified result.
Lean must elaborate and kernel-check every certificate before the report counts
it as resolved.

The report should include:

- the unique generated mutants and their provenance;
- their classifications;
- links or names for all proof artifacts;
- separated, equivalent/security-preserving, and unresolved counts; and
- search time and resource limits.

### Stage 6: Scale to cryptographic games

After the toy pipeline works end to end, replace its components incrementally:

- `SpecSyntax` becomes typed syntax for security games and adversary interfaces.
- `SpecSyntax.denote` maps that syntax to VCVio game semantics.
- `Scheme` becomes a cryptographic construction.
- Concrete input attacks become adversaries with checked advantage bounds.
- Candidate enumeration becomes proof search and adversary synthesis.
- Mutation operators cover quantifiers, oracle access, query timing, hypotheses,
  reuse conditions, and protocol bindings.

Keep the same result classifications and trust boundary. The cryptographic
system may leave many mutants unresolved; it must never turn search failure into
a security result.

### Recommended next milestone

Build a completely automatic version of the current finite toy example:

1. Express the toy definitions and constructions in typed syntax.
2. Generate the existing depth-one mutants rather than listing them manually.
3. Search the existing finite scheme and input catalogues.
4. Produce proof-carrying classifications.
5. Derive and print the coverage report from those classifications.

This milestone validates mutation generation, classification, certification,
and reporting before introducing cryptographic games.
