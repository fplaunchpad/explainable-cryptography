# Grouping arbitrary ciphertext products

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: machine-checked. Every ciphertext-valued minimum public recipe in
`Historical.General.frame` has an exact assembly of constructed encryptions
and honest indexed selectors. Arbitrarily nested products in this assembly
can be grouped into public contributions only, honest contributions only, or
both. The grouping preserves actual full-E values and publicness, and bounds
the needed observations against the original recipe size.

This connects the [mixed-ciphertext reduction](helios-mixed-ciphertexts.md) to
the existing minimum-origin classification. It does not establish transfer of
all public observations between vote worlds. Static equivalence and final
partial-decryption frames remain open.

## Assembly and grouping

[CiphertextGrouping.lean](../../ExplainableCrypto/Helios/Symbolic/CiphertextGrouping.lean)
defines `Historical.General.CiphertextAssembly n` with three constructors:

- `constructed k r p` retains arbitrary key, nonce and payload recipes.
- `honest (i, j)` denotes the actual indexed ciphertext selector on voter i.
- `mul a b` retains the complete product tree, including repeated leaves.

`recipe` interprets the assembly as an ordinary public-recipe term. The datatype
itself does not certify publicness or semantic key agreement. Those properties
remain explicit in the theorems.

`CiphertextGroup` distinguishes three nonempty cases. A `constructed r p`
group contains composed public nonce and added public payload recipes. An
`honest a` group contains a nonempty honest occurrence tree. A `mixed r p a`
group contains both. `merge` handles all nine pairs of cases, preserving the
relative contributions and repeated honest occurrences.

Absence is represented by the case distinction. The construction never inserts
a composition or multiplication unit, and never inserts a payload zero into
a public-only group. Zero-padding is justified later only when an actual honest
numeric contribution is present. This distinction is required by E0.

## Keys and full-E values

[CiphertextGroupingSoundness.lean](../../ExplainableCrypto/Helios/Symbolic/CiphertextGroupingSoundness.lean)
proves `CiphertextAssembly.key_agreement_of_value`: if the original recipe
is E-equal to a ciphertext under key K, every constructed leaf's key evaluates
to K, and every honest leaf binds K to the actual public key. The proof uses
full-E multiplication inversion and honest selector values. It permits keys
that agree only after reduction; literal syntactic equality is not required.
A public-only tree can use another common key.

`grouped_value` reconstructs the precise ciphertext under K. Its nonce and
message are `group.nonce` and `group.message`. For each merge, AC rearrangement
collects public and honest contributions without deleting occurrences.
Homomorphic fusion supplies the ciphertext value. Original subrecipes and
candidate values may be reducible, and no representative-normality premise is
imposed on the caller.

`assembly_of_ciphertext_syntax` refines the existing general-frame syntax
classification into exact constructed/honest-selector assembly leaves.
`minimum_ciphertext_grouping` then derives the complete certificate from:

- the actual general frame, either swap and arbitrary valid ground candidates;
- the caller's public-name policy and minimum public recipe;
- a supplied full-E ciphertext value with its key, nonce and message.

Its conclusion preserves equality to the original recipe, leaf key agreement,
group publicness, the original-size budget, a public smaller key recipe, and
E-equality of both grouped components to the supplied target components.
It does not assume an assembly or a factor-origin certificate. This grouping
result itself does not require freshness; the subsequent nonce-equality
characterization does.

## Bounds use the original recipe

Let |r| denote `r.nodeCount`. The group budget is:

| Group | Budget |
| --- | --- |
| `constructed r p` | `r.nodeCount + p.nodeCount + 2` |
| `honest a` | 2 |
| `mixed r p a` | `r.nodeCount + p.nodeCount + 3` |

`group_budget` proves that this budget is at most the original assembly recipe's
size. The honest budget is a lower bound, not an encoding-size formula for the
honest tree. A merge budget is at most the sum of its two input budgets plus
one; constructed and selector leaves supply the initial bounds.

`mixed_observations_smaller` derives strict bounds for r and `p + zero` against
the original recipe. `constructed_observations_smaller` bounds r and p when
no honest contribution is present. These conclusions do not rely on the size
of a regrouped canonical ciphertext recipe.

`keyRecipe` selects the leftmost constructed key, or the public-key handle at
an honest leaf. It is public under the original caller policy, strictly smaller
than the original recipe, and evaluates to the supplied semantic key. These
facts make key agreement available as a smaller public observation. The theorem
does not yet prove that such observations transfer between worlds.

## Claim ledger

All names below are under `ExplainableCrypto.Helios.Symbolic.Historical.General`.

| Claim | Evidence | Declaration | Scope |
| --- | --- | --- | --- |
| Grouping preserves nonce and message contributions | machine-checked | `CiphertextGroup.merge_nonce`, `merge_message` | All nine merges; E0 AC equations with no units |
| Publicness and the combined budget survive grouping | machine-checked | `CiphertextAssembly.group_public`, `group_budget` | Any assembly; arbitrary caller policy |
| Public key recipe is smaller and has the target key value | machine-checked | `CiphertextAssembly.keyRecipe_public`, `keyRecipe_smaller`, `keyRecipe_value` | Key-value theorem retains semantic leaf agreement |
| Every ciphertext value forces leaf key agreement | machine-checked | `CiphertextAssembly.key_agreement_of_value` | Actual general frames; arbitrary full-E target |
| Grouped ciphertext has the original E-value | machine-checked | `CiphertextAssembly.grouped_value` | Common semantic key, arbitrary tree and reducible inputs |
| Mixed nonce and padded payload observations are smaller | machine-checked | `CiphertextAssembly.mixed_observations_smaller` | Original assembly size and a mixed group |
| Every minimum ciphertext recipe admits the full grouping | machine-checked | `minimum_ciphertext_grouping` | Minimum public recipe and supplied ciphertext value; no assumed origin certificate |

## Controls and executable gate

[CiphertextGroupingSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/CiphertextGroupingSPOT.lean)
contains nine checked controls. Its fresh two-candidate fixture uses a nested
four-leaf assembly: two constructed encryptions and two occurrences of honest
index (0, 1). One constructed key is a projection wrapper around the public-key
handle. The key recipes differ syntactically but agree under E in both worlds.

The original recipe has 20 nodes. Its grouped nonce is `40 ◦ 41`, its public
payload is `80 + zero`, and its honest tree repeats index (0, 1) twice. The group
budget is 9. The exact grouping, strict original-size bounds, full-policy
publicness and equality to an independently written mixed recipe are checked.
The honest candidate fixture retains nonliteral E-equivalent bit values.

Negative controls establish that deleting the second public nonce factor changes
the result, and that a public wrong-key leaf prevents equality to every possible
ciphertext target. An honest-only input is not equal to a ciphertext obtained
by padding its nonce with zero. A public-only payload does not gain zero-padding.
These controls exclude accidental factor loss, unconditional fusion and silently
added units. A minimum representative of the positive fixture instantiates the
complete `minimum_ciphertext_grouping` conclusion while preserving its actual
value and full public-name restriction.

`CiphertextGroupingExperiments.lean` generates assembly trees to depth four,
with constructed and honest leaves and repeated indices. An independent
traversal lists the original public nonce leaves, public payload leaves and
honest indices. The gate compares these lists with the grouped contributions,
retaining multiplicity, and checks the original-size budget. Literal leaf
payloads are public names in this gate; arbitrary payload semantics are covered
by the proof and explicit controls, not claimed as randomized coverage.

The dropped-public-factor mutation fails at n=0, seed 1, with zero shrinks.
The corrected gate passes seeds 1, 7 and 42, each with 500 configured cases,
maximum size 40 and `gaveUp=0`, plus 256 deterministic inputs. Nine additional
directed root combinations exercise every merge case. This gate checks grouping
and budgets; it neither decides full E nor tests arbitrary protocol privacy.

## Reproduce and continue

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/CiphertextGroupingExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
python3 scripts/check_helios_claims.py
```

The full build passes (3462 jobs), including 24 new public theorem type/axiom
audits and eleven definition/type checks. Its 1151 nonempty axiom reports use
only `propext`, `Classical.choice` and `Quot.sound`; 17 more are axiom-free.
There are no warnings, errors or `sorryAx`. The local log is
`tmp/variable-overlap/ciphertext-grouping-full-build.log`. The source audit
checks 182 public theorem entries and selected stale claims in 12 current-status
documents; this does not replace elaboration or establish log freshness.

The reality oracle is Cortier–Smyth Appendix B.3's closure under combinations
of honest and freshly constructed ciphertexts. Trusted definitions remain
E/E0, public recipes, candidate validity, indexed selectors and minimum syntax
size. No cryptographic equation, public operation, custom axiom or confluence
assumption changed.

The subsequent [ciphertext induction step](helios-ciphertext-observations.md)
transfers key coherence and all nine grouped comparisons under the explicit
smaller-observation hypothesis. It derives the ciphertext-valued minimum-recipe
branch from these facts. The global smaller-observation argument and other
public recipe heads remain open. Minimum recipe existence is relative to a world; transferring a chosen
minimum syntax and its reductions also requires proof. Final partial-decryption
frames and historical process matching remain open. Preserve the full objective
in the canonical [task list](../../task%20list.md).
