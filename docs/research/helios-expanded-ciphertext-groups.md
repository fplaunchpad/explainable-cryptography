# Ciphertext groups over published handles

Status: machine-checked, component classification and bounded group-observation
transfer. Current milestone: [B8](helios-proof-blueprint.md).
[`expanded_group_ciphertext_eq_iff`](../../ExplainableCrypto/Helios/Symbolic/ExpandedGroupEquality.lean)
classifies equality of grouped ciphertext values into an explicit key equality
and the existing constructed/honest/mixed observation matrix. It applies to
public nonce and payload recipes using all expanded handles.

## Exact comparison matrix

A group contains public contributions, a nonempty honest combination, or both.
Public submissions and fresh names suffice for the expanded classification;
submission acceptance and minimum recipe size are unnecessary at this layer.

| Groups | Required observations |
|---|---|
| Constructed / constructed | Public nonce equality and public payload equality. |
| Honest / honest | Exact equality of honest index multisets, including duplicates. |
| Mixed / mixed | Equal honest index multisets, public nonce equality, and equality of public payloads padded with zero. |
| Different classes | False. |

For whole grouped ciphertexts, semantic key equality is an additional explicit
condition. Public remainders are not assumed equal across worlds. A present
honest numeric contribution justifies zero padding in the mixed row; zero
cannot be erased from arbitrary unpadded public payloads.

## Reuse and protection boundary

[`CiphertextGroup`](../../ExplainableCrypto/Helios/Symbolic/CiphertextGrouping.lean)
now takes a handle count, defaulting to three for existing callers. Its original
merge, component, publicness and size definitions are retained. The four merge
laws, public-policy weakening and bounded observation transfer are generalized
to any handle count. Existing initial-frame callers retain their three-handle
specialization. No new homomorphic computation or merge algebra is introduced.

Published trustee partials can contain restricted names while remaining opaque
to public observations. They fail the old raw `nonceSafe` predicate, so that
predicate cannot be silently assumed for expanded nonce remainders.
[`mixed_named_nonce_eq_iff_of_normal_factors`](../../ExplainableCrypto/Helios/Symbolic/MixedNonceProvenance.lean)
extracts the existing separation argument at its needed premise: normal
representatives have no protected outer name factors. The original strong
protection theorem and the new opaque theorem both use this shared argument.
The original strong-protection public statement remains unchanged.

[`OpaqueMixedNonces`](../../ExplainableCrypto/Helios/Symbolic/OpaqueMixedNonces.lean)
proves that opaque-protected values have normal protected representatives,
separates public remainder factors from honest nonce occurrences, and excludes
a mixed nonce from a purely honest group. Protected names inside opaque data
are allowed. Raw-unsafe supplied terms are also allowed when an E-equal safe
representative witnesses protection.

[`ProtectedGroupEquality`](../../ExplainableCrypto/Helios/Symbolic/ProtectedGroupEquality.lean)
uses these facts for the nine-case matrix in any opaque-protected frame whose
policy protects the honest nonces. Expanded wrappers derive that frame premise
from the actual published-frame protection theorem and public submissions.

## Bounds and assembly connection

`expanded_group_components_equality_swap` transfers component equality between
any swap assignments under observations below the sum of the two group bounds.
The existing observation-transfer proof leaves strict room for public nonce,
payload and zero-padded payload comparisons. It retains publicness and all
occurrence multiplicities.

The [expanded assembly theorem](helios-expanded-ciphertext-assemblies.md)
now connects these bounds to original minimum ciphertext recipe sizes. It
recovers exact constructed, honest-selector and multiplication syntax, derives
key agreement from ciphertext values in both frames, and closes the full
conditional minimum ciphertext equality branch using strictly smaller public
observations. The group matrix remains the shared component-classification
layer used by that theorem.

## Controls and evidence

Ten [kernel controls](../../ExplainableCrypto/Helios/Symbolic/ExpandedGroupSPOT.lean)
cover actual partial protection versus old raw safety; a reducible public alias;
retained duplicate honest nonces; rejection of mixed/pure-honest nonce equality;
cross-class ciphertext rejection; necessary payload padding; separate key
equality; a raw-unsafe but semantically protected remainder; generalized merge
laws; and bounded mixed component transfer. The bounded transfer control uses
a diagonal election to inhabit its explicit observation premise. Other controls
include different honest voters and actual published values in both swaps.

The [gate](../../ExplainableCrypto/Helios/Symbolic/ExpandedGroupExperiments.lean)
detects all three mutations at input zero, seed 1, zero shrinks: duplicate honest
nonce deletion, erased numeric padding, and the old strong raw-safety claim for
a public partial. Seeds 1, 7 and 42 each pass 500 cases at size 40, `gaveUp=0`;
all 2048 deterministic inputs pass. Fixtures cover both swaps, one through five
honest nonce occurrences, public partials, both result slots and delayed
projections. The gate checks executable raw leaf summaries on these fixtures;
it is not a decision procedure for full E or a security proof.

The gate passes 1048 jobs; the group generalization and initial callers pass
816 jobs; expanded component classification passes 931 jobs. Twenty new theorem
audits cover the increment. Full `lake build` passes 3703 jobs, including all
ten controls and the existing initial-frame callers. The integrated log has
2163 nonempty standard-only axiom reports, 20 axiom-free reports, and coverage
for 1197 public theorem entries and 63 current-status documents. Log:
`tmp/variable-overlap/expanded-group-full-build.log`. See the
[results ledger](helios-results.md).

Multiplication shared minimum transport,
other shared minimum cases, successful-case integration and the global B8
induction remain open. B9 historical process matching and B10 full secrecy
remain open. Milestone coverage remains seven of ten (70% unweighted).
