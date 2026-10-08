# Source process syntax and binding

[Historical symbolic ballot secrecy](helios-source-coordinated-phases.md)
is now machine-checked, integrated and audited. B1–B10 meet their acceptance
conditions. scopedVoterElection_ballot_secrecy proves source weak labelled
bisimilarity of the actual swapped scoped elections, for arbitrary valid ground
candidates and finite administration size under documented name, nonce/parameter
and channel freshness. SourceElectionRelation preserves all actual source actions,
complete frames, shared handle coordinates and private policies. The final
interface assumes no source correspondence, bisimulation or static equivalence.
The historical component-weeding protocol and documented tuple-tail correction,
full E/E0, attacker observations and rejection behavior are unchanged. Independent
positive/negative controls and both refuted shortcuts remain. The [retrospective reuse audit](helios-reuse-retrospective.md) is complete;
computational security is a separate extension.

B9 now has a finite static-channel process AST, capture-avoiding substitution
through entire continuations, source formula semantics, and direct ground
communication/conditional rules. These are machine-checked supporting results.
B9's operational correspondence and B10's source labelled bisimilarity remain
open. Blueprint coverage remains 8/10 (80%, unweighted).

[SourceProcessSyntax.lean](../../ExplainableCrypto/Helios/Symbolic/SourceProcessSyntax.lean)
defines null, parallel, input, output and conditional processes. Input changes
the free-variable type from `V` to `Option V`: `none` is the fresh variable and
`some v` is an old variable. Recursion under input uses the previously checked
`liftSubst`, preserving inner binders while substituting older variables. A
channel is a fixed natural-number name; channel variables are outside this
fragment. The indexed inductive lives in `Type 1`; this is a universe choice,
not an unbounded or executable interpretation of the process.

`Formula` has equality, disequality and conjunction, matching Figures 2/3 of
Cortier–Smyth. `Formula.Holds` first gives every free variable a ground message,
then uses full `EqE`. No executable normalizer is presumed complete. Its public
predicate checks every literal name against the frame's restricted-name policy.

[SourceProcessBinding.lean](../../ExplainableCrypto/Helios/Symbolic/SourceProcessBinding.lean)
proves process substitution identity and composition, input/environment
agreement, input/substitution commutation and bijective free-variable renaming.
The induction includes further nested inputs, both parallel components and
both conditional branches. These are exact syntax equalities, so do not depend
on cryptographic assumptions. `Formula.holds_subst` gives environment agreement
for guards; `Formula.holds_staticEq` transfers every public guard across statically
equivalent frames, including negative and conjunctive tests. Public substitution
and local flattening preserve the corresponding policy and truth semantics.

`Agent.CoreStep` contains ground communication, Then, Else, and parallel context
rules. A communication substitutes the transmitted message into precisely the
receiver's fresh binder. It is a direct substitution rule: the paper's atomic
Comm rule instead relies on extended-process active substitutions. That
connection is now derived by `Extended.message_communication` and
`Extended.coreStep_derivable` in the explicit variable/active fragment. Inversion proves that two isolated input/output
prefixes communicate exactly when their channels agree, with the prescribed
continuation. Null and isolated prefixes have no direct internal steps.
Conditional inversion characterizes exactly the semantically enabled branches.

The ten kernel controls in
[SourceProcessSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SourceProcessSPOT.lean)
retain independently chosen literal expectations: two inputs carry 40 and 41
into distinct positions while old variable 7 survives; a capture-all mutant
changes the output; channel 8 communicates with 8 but cannot communicate with
10; and `zero + one` is E-equal to `one` despite syntactic inequality. Thus the
syntactic-only guard mutant is rejected, and the negated equality in a conjunction
forces Else. Trustee and result communications use the actual source input
bodies and produce exactly the messages already connected to the B8 frames in
the [payload agreement](helios-source-payloads.md).

These are routine structural laws and explicit kernel controls, so this increment
does not add a randomized campaign. Earlier term/payload tests retain their
bounded status. Failed elaborations were proof-engineering issues: polymorphic
recursive substitution needed explicit type indices, a let-bound control needed
unfolding, and a numeric equation was initially addressed through the wrong
namespace. No mathematical claim was weakened in response.

Literal residuals, evaluated visible correspondence and captured-frame agreement
are now checked. The remaining bridge must extend the active-variable fragment
with name restrictions/scope, establish the full operational converse and outer voter construction, and justify arbitrary source fresh
exported-variable naming. Variable closedness/unique definitions are now
certified for actual frames, ground lets, captures and their current-rule targets. This AST alone is not the full source calculus;
its free-variable renaming theorem is not a theorem of name alpha-equivalence.
Replication and dynamically chosen channels are not represented here. The
historical election is finite and uses static channels, but a source closure
argument must still establish that the chosen representation suffices. There
is no new claim of full protocol privacy from the core reductions alone.

Integrated verification for the plain-process checkpoint: `lake build` passes **3779 jobs**, with
**2518** nonempty standard-only and **27** axiom-free reports. The claim audit
covers **1559** public theorem entries and **78** current-status documents.
All five changed Lean sources have current oleans; **985** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-process-full-build.log`. This increment
adds 27 theorem audits, including ten kernel controls, and seven definition
checks. Targeted controls pass 1011 jobs.
