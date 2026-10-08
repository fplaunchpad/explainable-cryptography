# Ciphertext assemblies over published handles

Status: machine-checked, conditional minimum ciphertext equality.
Current milestone: [B8](helios-proof-blueprint.md).
[`accepted_expanded_minimum_ciphertext_equality_swap`](../../ExplainableCrypto/Helios/Symbolic/ExpandedCiphertextTransport.lean)
transfers ciphertext equality between any two swap assignments in the actual
expanded frame. It derives exact assemblies, common-key agreement in both
worlds, and comparison bounds from the original minimum recipes.

## The checked statement

The theorem assumes fresh names, valid ground candidate substitutions, public
submitted recipes, and their sequential acceptance in the original false-swap
frame. Both compared recipes are minimum in the supplied source expanded frame
and have ciphertext values there. Equality observations for public recipe pairs
strictly below their combined node count remain an explicit premise.

Its conclusion is an iff between equality of the two evaluated recipes in the
source and destination frames. Destination minimum size, a grouping certificate
and common-key agreement are all derived or unnecessary. The observation
premise still requires the unfinished global B8 induction.

## Reused representation and proof

[`CiphertextAssembly`](../../ExplainableCrypto/Helios/Symbolic/CiphertextGrouping.lean)
now takes a handle count, defaulting to three. Constructed leaves contain
arbitrary key, nonce and payload recipes over that frame; honest leaves retain
an indexed original ciphertext selector; multiplication retains the full tree.
The existing three-handle recipe/key interfaces remain available to old callers.
[`recipeWith` and `keyRecipeWith`](../../ExplainableCrypto/Helios/Symbolic/AssemblyHandleSyntax.lean)
interpret honest leaves through a supplied old-handle embedding.

[`AssemblyHandleTools`](../../ExplainableCrypto/Helios/Symbolic/AssemblyHandleTools.lean)
proves publicness, a strict selected-key size bound, and a group bound measured
against the original assembly recipe. It derives leaf key agreement by full-E
ciphertext inversion and proves grouped interpretation with the existing E3
rule and generic group merge laws. No new homomorphic law is introduced.

[`ExpandedCiphertextAssembly`](../../ExplainableCrypto/Helios/Symbolic/ExpandedCiphertextAssembly.lean)
instantiates the honest-selector equations in the actual expanded frame.
Numeric result origins exclude ciphertext leaves hidden in publication slots.
The existing minimum syntax theorem then recovers the exact assembly.
`expanded_assembly_equality_iff` reduces actual recipe equality to a separate
selected-key equality and the checked nine-case group observation matrix.

The final proof uses the existing accepted forward ciphertext-value theorem to
obtain ciphertext values in the destination. Full-E inversion supplies key
agreement there too. Strictly smaller observations transfer key equality and
the group matrix, including zero-padded mixed payloads. The proof preserves
public policies, opaque trustee data and every repeated honest occurrence.

## Controls and evidence

Eight [kernel controls](../../ExplainableCrypto/Helios/Symbolic/ExpandedAssemblySPOT.lean)
cover a four-node reducible selected key; exact mixed syntax and its original
size bound; actual grouped values with published partials/results; rejection of
wrong-key fusion; rejection of a published partial selector as a ciphertext;
rejection of a deleted honest occurrence; an actual minimum selector's assembly
certificate; and an inhabited instance of the final conditional theorem that
rejects different honest nonces. The last uses a diagonal election to supply
its observation premise. Other controls use different candidates in both swaps.

The [gate](../../ExplainableCrypto/Helios/Symbolic/ExpandedAssemblyExperiments.lean)
detects all three deliberate mutations at input zero, seed 1, zero shrinks:
incoherent-key fusion, treating a partial selector as a ciphertext, and claiming
every selected key has one node. Seeds 1, 7 and 42 each pass 500 cases at size 40,
`gaveUp=0`; all 2048 deterministic inputs pass. Generated trees include a mixed
base, zero through four extra leaves, published partial/result subrecipes and
nonliteral keys, in both assignments. Executable normalized leaf summaries
provide bounded refutation evidence, not a decision procedure for full E.

Targeted checks pass: gate 1050 jobs, generic tools 817 jobs, complete conditional
transport 943 jobs, and all eight controls 1080 jobs. Twenty-one public theorem
audits and two definition checks cover this increment. Integrated verification
is recorded in the [results ledger](helios-results.md).

## Remaining frontier

The [observation assembly](helios-expanded-observation-assembly.md) now combines
all value branches and reduces the exact final-frame target to two-way shared
minima. [Non-ciphertext multiplication](helios-expanded-multiplication-minima.md)
now closes its local shared-minimum case. [Constructed ciphertext minima](helios-expanded-constructed-minima.md)
close constructor transport and the constructed-only product case. Mixed products, remaining local/successful cases and global shared-minimum
transport remain open. B8 final-frame equivalence, B9 process matching and B10 full
symbolic secrecy remain incomplete. Milestone coverage stays seven of ten
(70% unweighted); it does not estimate effort remaining.


Integrated verification: full `lake build` passes 3709 jobs, including all
21 new theorem audits, two definition checks and eight kernel controls. The
log contains 2184 nonempty reports using only `propext`, `Classical.choice` and
`Quot.sound`, plus 20 axiom-free reports. The claim checker covers 1218 public
theorem entries and 64 current-status documents. Log:
`tmp/variable-overlap/expanded-assembly-full-build.log`.

Honest-only combinations now have [global expanded-frame minima](helios-expanded-honest-minima.md)
and need no smaller premises for shared transport. Exact indexed occurrences
exclude honest groups from nonminimum ciphertext products with minimum children.

[Expanded mixed compression](helios-expanded-mixed-compression.md) now closes
mixed products with at least two public constructors under two-way smaller
minima. Minimum mixed competitors have exactly one constructor and preserve
honest indices, public nonce equality and zero-padded payload equality. The
remaining mixed case needs global padded payload minima with published numeric
handle costs.

[Expanded padded minima](helios-expanded-padded-minima.md) now close the general
one-constructor mixed case using published numeric-handle costs and shared
padded values. All multiplication local cases are assembled under the two
smaller-minimum hypotheses. Remaining pair/selector and successful-case
transport and the global simultaneous induction stay open.
