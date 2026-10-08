# Recipe input through active frames

B9 now derives every evaluated recipe input from source In and active Subst
beside the actual public frame. The original recipe remains the label; its
received value is evaluated by the frame's active substitutions. All bindings,
parallel context and nested input binders are retained. Internal steps also
have source derivations beside their actual public frames. Together with the
previous output bridge, all three evaluated step kinds have forward derivations
in the variable/active fragment. These are machine-checked supporting results.
The full source converse, name scope/alpha, source well-formedness and final
bisimilarity remain open; B9/B10 stay at 8/10 milestones (80%, unweighted).

## Explicit active substitution

[SourceFrameSubstitution.lean](../../ExplainableCrypto/Helios/Symbolic/SourceFrameSubstitution.lean)
defines the sequential substitution performed by the finite collection of
actual active bindings. `entriesSubst_value` proves that distinct variable
names receive their own full ground value. Values need not differ: two separate
handles may have equal payloads. Ground terms and processes are unchanged by
subsequent variable substitution.

`subst_beside_context` rearranges parallel syntax to bring one active binding
into contact with the plain continuation, uses source Subst, then restores the
parallel frame. `frameEntries_apply` repeats this explicit derivation for all
bindings. `activeFrame_apply` proves that the actual public active frame
evaluates any plain process over its handle domain, including below later input
binders, while leaving every frame binding intact. It adds no primitive
whole-frame evaluation rule.

The explicit frame exports exactly its listed variables. `activeFrame_exports`
proves that every variable available to an input recipe is actually defined by
an exported active substitution. This domain theorem does not by itself prove
full source admissibility for arbitrary extended processes. Unique-definition
and closedness certificates/preservation for the actual variable/active frames
are now proved using their complete exported domains.

## Input and internal derivations

[SourceFrameInput.lean](../../ExplainableCrypto/Helios/Symbolic/SourceFrameInput.lean)
proves that binding the literal recipe and then applying the active frame gives
exactly the continuation bound to the recipe's evaluated ground value. A newer
input binder remains local. `frame_input_in_context` first applies source In
with the literal recipe, then uses the active Subst derivation on its continuation
and untouched ground parallel context. Acceptance is not required at input.

`frame_visible_input_derivable` uses exact input-prefix/context inversion and
ParEq to cover every evaluated visible input. `scoped_input_derivable` connects
every public recipe-labelled wrapper input to a source step with the same recipe
label and exact full target frame/process. It begins with an already-public
scoped input; it does not derive name-restriction filtering from source name
Scope. In particular a recipe's publicness concerns its literal names, not
restricted atoms inside a value obtained through a public handle.

[SourceFrameInternal.lean](../../ExplainableCrypto/Helios/Symbolic/SourceFrameInternal.lean)
derives evaluated internal core and Tau steps in an arbitrary public variable
domain. The actual active frame can therefore remain beside the election body.
`scoped_tau_derivable` retains that exact frame and derives the internal step
using atomic communication, active lets, semantic conditionals and source
parallel/structural closure. It complements the earlier frame-free derivation.

These results and the [atomic output bridge](helios-source-atomic-output.md)
now cover the forward derivation of every evaluated step kind beside actual
public active substitutions. They do not classify every reduction permitted by
the eventual full source calculus.

## Controls and remaining obligations

Eleven controls in
[SourceFrameInputSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SourceFrameInputSPOT.lean)
use a two-handle frame containing a public key and another name. A compound
recipe reverses their positions; an independently written continuation retains
that compound value separately from a later input variable. Source input and
active substitution reach those exact expressions. Reversing the handle values
or capturing the newer binder changes the result. A source input cannot discard
old exported bindings. The handle recipe is public although its key value
contains a restricted atom; a literal use of that atom is not public.
Equal-valued distinct handles still evaluate correctly. Actual honest-ballot
replay input reaches its pending guard with label var 1, and the actual first
private honest handshake retains its initial public-key frame.

These structural derivations and kernel controls add no randomized security
campaign. The reality oracle is Figure 3 In/Subst/Par/Struct, the source's
exported active frames and Figure 4's input followed by a separate guard.
Variable well-formedness and preservation for actual frames, lets and captures
are now proved. Next connect outer voter construction, add name restriction/
scope and source alpha-equivalence, and prove the full operational converse. Then combine actual observations and transitions into
source weak labelled bisimilarity and full symbolic secrecy. The maintained
[blueprint](helios-proof-blueprint.md), [source active bridge](helios-source-active.md)
and [task list](../../task%20list.md) retain those obligations.

Integrated verification for the active-frame input checkpoint: `lake build` passes **3826 jobs**, with
**2780** nonempty standard-only and **44** axiom-free reports. The claim audit
covers **1838** public theorem entries and **86** current-status documents.
All six changed Lean sources have current oleans; **1070** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-frame-input-full-build.log`. This
increment adds 27 theorem audits, including eleven kernel controls, and one
definition check. Targeted controls pass 1204 jobs. Freshness/hole/link evidence:
`tmp/variable-overlap/source-frame-input-verification.txt`.
