# Minimum addition recipes with published numerals

Status: machine-checked. Current milestone: [B8](helios-proof-blueprint.md).
[`accepted_expanded_minimum_children_add_shared`](../../ExplainableCrypto/Helios/Symbolic/ExpandedAddMinimumClosure.lean)
closes addition shared minimum transport in actual accepted expanded frames.
Together with [addition equality](helios-expanded-addition.md), this discharges
the local addition obligations needed by the future global induction.

## Public theorem

Assume fresh names, arbitrary valid ground candidates, public submissions
accepted in sequence, and any two swap assignments. If `a` and `b` are minimum
public recipes in the source expanded frame `φ`, then their addition has a
shared source-minimum representative in `φ` and the destination frame `ψ`:

```text
∃ s, MinimalRecipe ns.restricted φ.value s ∧
  EqE (φ.eval (add a b)) (φ.eval s) ∧
  EqE (ψ.eval (add a b)) (ψ.eval s).
```

The theorem derives a shared numeric tally table from acceptance. It has no
smaller-observation premise, no destination-minimality premise and no remaining
local numeric-cost assumption. The original sum need not itself be minimum:
published zero plus published one can collapse to a one-node result handle.

## Least numeric cost

Literal syntax costs are insufficient when any published numeral has a
one-node handle. Greedy denomination choice also fails: with published values
3 and 4, target 6 uses 3+3 more cheaply than 4+1+1.

[`NumericHandleCosts`](../../ExplainableCrypto/Helios/Symbolic/NumericHandleCosts.lean)
defines pure numeric expressions from zero, one, marked numeric handles and
addition. `numericHandleCost` is the least attainable node-count-plus-one for
a present number. Its definition uses natural-number well ordering, with a
literal numeral proving that the set is nonempty. Every cost is attained by a
public pure numeric expression; this is proved, not assumed. Absence costs
zero, while every present numeral costs at least two. Both bits and every
marked numeric handle attain cost two. Combining realizers proves subadditivity.

This is a logical minimum, with no claimed executable full-E decision procedure
or generally verified greedy/coin algorithm. It is defined over pure numeric
syntax before the global semantic minimum theorem is proved.

## From summary cost to global minimality

[`NumericHandleRealization`](../../ExplainableCrypto/Helios/Symbolic/NumericHandleRealization.lean)
realizes every valid nonempty addition summary at its exact atom-plus-numeric
cost, retaining every nonnumeric recipe occurrence. Equal handle-aware syntax
summaries imply E-equality under any substitution satisfying the numeric table.
That sound direction needs no atom irreducibility: expansion at the recipe
level reduces it to the existing raw E0 summary theorem.

For global minimality, actual source-minimum nonnumeric leaves are semantic
addition atoms by the expanded origin theorem. Equal semantic values then have
equal numeric contributions and equal bags of full-E atom classes. Existing
minimum-leaf cost equality transfers the atom costs. Compare an exact-cost
representative against an arbitrary public minimum equivalent, whose raw syntax
must pay at least the same summary cost. This establishes global minimum size
against all public recipes, including recipes with destructors.

The final shared-minimum theorem applies this argument to the addition of two
minimum children. Both accepted frames satisfy the same numeric table, so the
constructed source-minimum representative is equal to the original sum in both.
The caller's public-name policy is preserved in the general source theorems.

## Controls and evidence

Eight [kernel controls](../../ExplainableCrypto/Helios/Symbolic/ExpandedAddMinimumSPOT.lean)
cover a collapsing numeric sum with a shared minimum; a mixed public-name/result
sum for different honest voters; globally minimum name-plus-zero and duplicated
name expressions; failure of exact raw cost when an atom is nonminimum; an
actual accepted one-node tally of two; absent versus present-zero cost; the
3+3 greedy counterexample; and a false transport when the destination does not
satisfy the shared numeric table.

The [gate](../../ExplainableCrypto/Helios/Symbolic/ExpandedAddMinimumExperiments.lean)
compares dynamic programming against independent enumeration of denomination
multiplicities. It detects all three mutations (greedy choice, literal lower
bound, free present zero) at input zero with seed 1 and zero shrinks. Seeds 1,
7 and 42 each pass 500 cases at size 40 with `gaveUp=0`; all 4096 deterministic
inputs pass. The finite domain includes denominations 0 through 5, targets 0
through 12, and subadditivity checks. This refutation gate is not a proof that
the executable algorithm computes the logical minimum for all inputs. The
kernel control relates them on the concrete greedy counterexample.

Targeted builds pass for costs, realization (888 jobs), global closure (948
jobs), and all controls (1063 jobs). Thirty-one new theorem audits and three
definition checks cover the increment. Full `lake build` passes 3692 jobs with
2124 nonempty standard-only axiom reports, 20 axiom-free reports, 1158 public
theorem audit entries and 61 current-status documents. Log:
`tmp/variable-overlap/expanded-add-min-full-build.log`. See the
[results ledger](helios-results.md).

## Remaining proof

Multiplication shared minimum transport, remaining shared minimum transport,
successful-case integration and the global expanded-frame induction remain
open. B9 historical process matching and B10 full secrecy remain open. This
local transport theorem does not establish final-frame static equivalence or
protocol privacy by itself.
