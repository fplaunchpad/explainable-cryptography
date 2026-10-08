# Source variable definitions and closedness

B9 now certifies unique active definitions and variable closedness for every
actual frame/process state, fresh ground let and raw captured output state.
The variable/active rules preserve unique definitions. Actual frames export
their whole available variable domain, and that stronger property proves
well-formedness of every structural, internal, free-label and bound-output
target in this fragment. These are machine-checked supporting results.
Name scope/alpha, the full operational converse and outer voter construction
remain open before final source bisimilarity; B9/B10 stay at 8/10 milestones
(80%, unweighted).

A retained counterexample refutes a broader claim: arbitrary syntactic closedness
is not preserved by unrestricted raw EqE Rewrite. Inserting an undefined variable
into a discarded projection argument preserves E equality but changes syntactic
free variables. The actual-frame preservation theorems use complete exported
domain coverage, not that false generalization. This is a model-boundary control,
not an election privacy attack or a claim that the paper's full admissible
source calculus has been characterized.

Global base-name/channel permutation equivariance is now also proved for the
current rules; see the [name-permutation record](helios-source-name-permutations.md).
This prerequisite does not add actual name restriction or discharge alpha-
equivalence, the full source converse or outer voter construction.

## Definitions and scope

[SourceVariableScope.lean](../../ExplainableCrypto/Helios/Symbolic/SourceVariableScope.lean)
defines `VarsIn` for terms, formulas and plain processes. Every term position is
checked, including all proof fields and both conditional branches. Input permits
its newly bound None variable and shifts every old variable through Some.
Scope monotonicity and substitution preservation are proved for all three
syntactic layers, including arbitrary nested inputs.

[SourceUniqueDefinitions.lean](../../ExplainableCrypto/Helios/Symbolic/SourceUniqueDefinitions.lean)
defines `UniqueDefinitions` recursively. Parallel components must export disjoint
variable domains, and every variable restriction must contain an exported
definition for its newly bound None variable. The recursive condition ensures
that this definition is unique. Plain input binders require no active alias;
they are bound by their input prefix.

Injective renaming preserves uniqueness, including under restrictions. The
renamed export domain is exactly the image of the original domain, and shifting
an old context introduces no definition of the fresh variable. All current
structural rules preserve uniqueness, including Alias/Subst/Rewrite and fresh
New-Par. This invariant concerns variable definitions; name scope and the full
source rule set are still outside the fragment.

## Actual state certificates

[SourceWellFormedStates.lean](../../ExplainableCrypto/Helios/Symbolic/SourceWellFormedStates.lean)
extends scope checking to extended processes. `Closed` means that every free
variable use or active domain is covered by the whole process's exported
bindings. Parallel components share that scope; variable restriction binds None.
`WellFormed` combines `UniqueDefinitions` and `Closed` for this fragment.

`frameEntries_unique` uses injective variable names, without requiring distinct
payload values. `activeFrame_wellFormed` and `frameProcess_wellFormed` certify
all canonical public frames and evaluated process states, with no cryptographic
freshness, accepted-sequence or reachability premise. `letTerm_unique` supplies
the one required local definition and `ground_let_wellFormed` certifies actual
ground lets, even with later input binders. `frame_capture_wellFormed` certifies
the raw bound-output state before canonical last-handle renaming: exactly one
fresh definition is added and all old definitions remain separate.

## Preservation and the raw-rewrite boundary

[SourceWellFormedPreservation.lean](../../ExplainableCrypto/Helios/Symbolic/SourceWellFormedPreservation.lean)
proves unique-definition preservation for internal, free-labelled and bound-output
steps. A bound output from a uniquely defined source really exports an active
binding for its new variable. A raw variable restriction lacking its definition
would not justify that conclusion.

The complete-domain property is preserved by structural/internal/free-labelled
steps and extended by bound output. It implies closedness because every available
free variable is defined. The `frameProcess_*_target` theorems discharge both
properties for arbitrary targets of actual frame/process states in the current
rules, not only their prescribed canonical targets. This also covers inverse
EqE rewrites without assuming they preserve an arbitrary syntactic free-variable
set. These results do not assert preservation under source rules that have not
yet been implemented.

## Controls and remaining obligations

Eleven controls in
[SourceWellFormedSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SourceWellFormedSPOT.lean)
reject duplicate definitions even with equal payloads, a restricted variable
without its alias, and an undefined variable in the fourth proof field. Ordinary
input binding and a ground let with a later input remain valid. Equal payloads
under distinct variable names are valid. All actual historical stage forms and
the raw captured-output fixture have well-formed representations.

The raw-rewrite counterexample starts with one defined variable in a two-variable
ambient type. Rewriting name 40 to fst(pair(name 40, var 1)) introduces an
undefined use of variable 1 while preserving E. It remains uniquely defined but
is not closed. A second control shows that the same rewrite stays well-formed
when variable 1 actually has its own binding. Thus the complete-domain premise
used in the preservation theorem is substantive and supplied by actual frames.

These structural invariants and kernel controls add no randomized security
campaign. The reality oracle is the source's one-active-definition condition,
exactly one definition under variable restriction, and its bound-or-defined
notion of closedness around Figure 2. Next implement name restriction/scope and
source alpha-equivalence, connect the outer voter construction/lets, and prove
the full operational converse. Then assemble source weak labelled bisimilarity
and full symbolic secrecy using the [input/frame bridge](helios-source-frame-input.md)
and [output bridge](helios-source-atomic-output.md). The maintained
[blueprint](helios-proof-blueprint.md) and [task list](../../task%20list.md)
keep B9/B10 open.

Latest integrated verification: `lake build` passes **3831 jobs**, with
**2826** nonempty standard-only and **46** axiom-free reports. The claim audit
covers **1886** public theorem entries and **87** current-status documents.
All seven changed Lean sources have current oleans; **1080** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-wellformed-full-build.log`. This
increment adds 48 theorem audits, including eleven kernel controls, and eight
definition checks. Targeted controls pass 1209 jobs. Freshness/hole/link evidence:
`tmp/variable-overlap/source-wellformed-verification.txt`.
