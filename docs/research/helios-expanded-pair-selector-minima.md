# Expanded pair and selector minima; remaining successful roots

Status: machine-checked. Pairing and both selector operators now have local
shared-minimum transport without smaller-observation or smaller-minimum
premises. The full local assembly reduces [B8](helios-proof-blueprint.md) to
successful decryption and successful proof checking in both directions.

## Reuse honest data through retained recipes

[`ExpandedOldRecipeTools`](../../ExplainableCrypto/Helios/Symbolic/ExpandedOldRecipeTools.lean)
proves that variable-handle renaming preserves exact syntax size and reuses B7
for all public comparisons between retained old recipes, in either assignment
orientation. When every expanded minimum competitor of an old recipe still
uses old syntax, its actual expanded minimum is therefore shared. This argument
does not assume minimum sizes transfer across frame presentations.

[`expanded_minimum_honest_field_old`](../../ExplainableCrypto/Helios/Symbolic/ExpandedHonestFieldTransport.lean)
classifies any source-minimum recipe matching an honest field. Ciphertext
combination origins handle encrypted fields. Opaque nonce protection excludes
newly constructed proof matches; borrowed proof origins supply retained syntax.
The same minimum match then transfers by B7 without a smaller-test premise.

Choosing a global minimum competitor and applying the old field-size theorem
shows that every public recipe matching field `k` costs at least `k + 1` nodes,
even with all new handles available. This uniform bound retains the shorter
one-candidate component/aggregate alias. Every field selector has a shared
minimum; the original selector itself need not be minimum.

## Exact nonempty tails and safe selector transport

[`ExpandedHonestTailMinima`](../../ExplainableCrypto/Helios/Symbolic/ExpandedHonestTailMinima.lean)
uses the field-cost bound to rule out a constructed pair as a minimum match to
a nonempty honest tail. Remaining borrowed tails have exact voter/position
identity. Every nonempty tail is globally minimum at `k + 1` nodes, and every
minimum equivalent has exactly the same raw syntax. The first empty tail is
literal bottom in every assignment and uses that one-node shared minimum.

[`expanded_minimum_child_projection_shared`](../../ExplainableCrypto/Helios/Symbolic/ExpandedPairMinimumTransport.lean)
covers every `fst`/`snd` of a source-minimum child. A constructed pair returns
its minimum child; borrowed fields/tails use the origin results; a stuck
projection remains minimum. Fresh names, public submissions and numeric source
results are explicit. Acceptance supplies the numeric premise in the wrapper.

`accepted_expanded_minimum_children_pair_shared` covers pairs of minimum
children. An explicit minimum pair competitor establishes minimum size for the
original pair. A borrowed-tail competitor is shared through the unconditional
field/tail match theorems. Pairing minimum children can still produce a
nonminimum pair, and the theorem permits that required compression.

## Reduce final equivalence to two successful cases

[`ExpandedRootAssembly`](../../ExplainableCrypto/Helios/Symbolic/ExpandedRootAssembly.lean)
combines every operator and atom case into the generic simultaneous local
minimum interface. It reuses `Frame.DecryptCheckTransport` for the only remaining
local cases: successful decryption and successful proof checking. Stuck cases
of both operators are already closed.

`accepted_expanded_common_minima_of_decrypt_check_both` applies the existing
simultaneous strong induction once both orientations of that successful-root
transport are supplied. Conditional theorems then establish expanded, actual
partial and actual final static equivalence from those same two premises.
No separate global observation or common-minimum premise remains at this
interface. The successful-root transport premises themselves remain unproved;
this is not an unconditional final-frame privacy theorem.

## Controls and gate

The [gate](../../ExplainableCrypto/Helios/Symbolic/ExpandedPairMinimumExperiments.lean)
checks canonical field/remainder reconstruction for one through five candidates,
every nonempty tail, both voters and both swaps. It includes the one-candidate
aggregate alias and empty remainders. Three deliberate defects are detected at
input zero, seed 1, zero shrinks: minimum children forcing minimum pairing,
pair eta on a published partial, and distinct empty tails. Seeds 1, 7 and 42
each pass 500 cases at size 40 with `gaveUp=0`; all 2048 deterministic inputs
pass. These raw-normalized tuple fixtures are bounded checks, not a full E
decision procedure or global minimum-size proof.

Eight [pair/selector kernel controls](../../ExplainableCrypto/Helios/Symbolic/ExpandedPairMinimumSPOT.lean)
cover exact nonempty-tail minima and origins; a five-node pair of minimum
selectors with a one-node shared minimum; both honest selector operators;
constructed minimum pairs with arbitrary handles, including published partials
and results; the empty-tail boundary; the four-to-three-node one-candidate
aggregate alias; stuck partial projections and failed eta; and the necessity
of minimum size for exact origins. Direct shared controls use actual
different-vote frames and the existing nonliteral vote representatives.

A ninth [pipeline control](../../ExplainableCrypto/Helios/Symbolic/ExpandedRootAssemblySPOT.lean)
inhabits both remaining transports for equal-candidate frames using actual
minimum existence. It applies the conditional pipeline to all expanded,
partial and final public observations. It validates the interface and does not
discharge the residual successful cases for arbitrary different candidates.

## Remaining frontier

B8 local transport has ten of twelve operator cases complete. Only the
successful branches of `dec` and `checkspk` remain; their stuck branches are
checked. The conditional local/global assembly and presentation lifting are
complete. B8 remains open until both successful-root transport directions are
proved. B9 process matching and B10 full symbolic secrecy also remain open.
Overall coverage stays seven of ten top-level milestones (70% unweighted,
not effort or time remaining). See the [results ledger](helios-results.md)
for integrated verification.

Integrated verification: full `lake build` passes 3743 jobs, with twenty-nine
new public theorem audits and all nine kernel controls. The log contains 2328
nonempty reports using only `propext`, `Classical.choice` and `Quot.sound`, plus
21 axiom-free reports. The claim checker covers 1363 public theorem entries and
71 current-status documents. Log: `tmp/variable-overlap/expanded-pair-min-full-build.log`.

[Expanded successful-check transport](helios-expanded-successful-checks.md) now
closes `checkspk`, retaining whole-ciphertext binding and exact honest combination
origins. The remaining local interface for all three frame presentations is
successful decryption in both directions; B8 local coverage is now 11/12.

[Expanded public decryption](helios-expanded-public-decryption.md) now closes
direct E5 and constructed-partial E6. The remaining local case is complete
borrowed trustee tally-binding transfer for minimum ciphertexts. B7 handles
retained old recipes; general nested new-handle binding remains unproved.
