# Public probes for partial-key decryption

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: machine-checked. For decryption with a partial-decryption-valued key
argument and a ciphertext-valued second argument, three smaller public equality
probes preserve matching across the initial-frame swap. Minimum source recipes
therefore remain stuck in the destination. This closes both directions of the
equality branch for two minimum decryptions with these argument values.

The result covers all positive candidate counts and all valid ground candidate
substitutions, including reducible representatives. It uses the full name
policy, source minimum size and the explicitly assumed smaller-observation
hypothesis. It requires neither freshness nor destination minimum size.
General reverse transfer, arithmetic, arbitrary-recipe closure and full static
equivalence remain open.

## Matching as full-E component equality

[DecryptionProbes.lean](../../ExplainableCrypto/Helios/Symbolic/DecryptionProbes.lean)
proves that semantic matching data yields an actual reachable E5/E6 match.
`DecryptionMatch.exists_of_values` takes a ciphertext E-value and either a
direct-key E-value or a partial-decryption E-value bound to the complete supplied
ciphertext. It normalizes the ciphertext, aligns the key through full-E
injectivity, and constructs matching argument paths. The reachable plaintext
may be a reduced representative of the supplied plaintext.

`DecryptionMatch.exists_iff_values` gives the converse as well. It does not infer
matching solely from equality between the entire decryption and a chosen output;
it retains the actual key and ciphertext components needed by E5/E6.

For `b =E penc(key,nonce,payload)`, `DecryptionMatch.partial_key_iff` specializes
this relation to the explicit argument `partialDecrypt(a,binding)`:

```text
There is a reachable match iff
  key =E pk(partialDecrypt(a,binding))
  or (key =E pk(a) and binding =E b).
```

The first alternative is E5. The source model is unsorted, so a partial-decryption
term can itself be a secret key. The second alternative is E6 and retains the
complete ciphertext binding. Omitting either the E5 alternative or the binding
comparison is refuted by a checked counterexample.

## Three smaller public probes

[PartialKeyObservationInduction.lean](../../ExplainableCrypto/Helios/Symbolic/PartialKeyObservationInduction.lean)
uses the exact characterization with a public key recipe `k` for the ciphertext
argument `b`. Assume `|k| < |b|`. For
`r = dec(partialDecrypt(a,binding),b)`, the observations are:

| Public comparison | Role |
| --- | --- |
| `k =E pk(partialDecrypt(a,binding))` | Direct E5 key match |
| `k =E pk(a)` | E6 inner-key match |
| `binding =E b` | E6 complete ciphertext binding |

Each comparison's total node count is strictly below `|r|`.
`partial_key_match_transfer` applies to arbitrary frames with a common handle
type and name policy. Both ciphertext values use the corresponding evaluation
of `k`; their nonce and plaintext values may differ across frames. The theorem
requires publicness, the strict key-recipe bound, those two ciphertext values
and `Frame.ObservationsBelow` at `|r|`.

`Historical.General.assembly_partial_key_match_swap` discharges the two
ciphertext-value premises for arbitrary coherent ciphertext assemblies.
Constructed ciphertexts, honest ciphertext selectors and arbitrary coherent
products are included. Only source coherence is assumed. Existing smaller key
comparisons derive destination coherence; grouping then supplies both actual
ciphertext values. The assembly key recipe is public and strictly smaller than
the original ciphertext recipe.

## Minimum recipes and two-sided equality

`minimum_partial_key_decryption_failure` starts with an arbitrary minimum recipe
`dec(a,b)` in the source initial frame. Its supplied source values say that `a`
is E-equal to a partial-decryption constructor and `b` is E-equal to a ciphertext.
Minimum subterms and the existing exact origin theorem force explicit
partial-decryption syntax for `a`. Minimum ciphertext origins derive the
assembly syntax for `b`, including its coherence. These certificates are
conclusions of existing proofs, not new public premises.

The three probes preserve the existence of any match. The source minimum cannot
match, because the existing plaintext reconstruction would supply a smaller
public equivalent. Thus the destination cannot match either. Supplied target
arguments may reduce; the theorem assumes no destination value, normality,
minimum size or stuckness.

`minimum_partial_key_decryption_equality_swap` applies this failure result to
two source minimum decryptions whose first arguments have partial-decryption
values and whose second arguments have ciphertext values. Each individual
recipe-size bound fits below the original comparison's total size. Full-E
stuck-decryption injectivity then reduces both equality directions to the two
ordered argument comparisons, which are also strictly smaller. This is an iff
result for this argument class. It does not classify other possible argument
values or complete the whole stuck-decryption branch.

## Claim ledger

Names below are under `ExplainableCrypto.Helios.Symbolic`; `General` abbreviates
`Historical.General`.

| Claim | Evidence | Declaration | Scope |
| --- | --- | --- | --- |
| Semantic matching data yields actual paths | machine-checked | `DecryptionMatch.exists_of_values` | Arbitrary reducible terms, direct or partial key, complete ciphertext binding |
| Reachable matching has exactly such semantic data | machine-checked | `DecryptionMatch.exists_iff_values` | Existential plaintext; E5 and E6 |
| Partial-key matching is the exact three-probe formula | machine-checked | `DecryptionMatch.partial_key_iff` | Supplied ciphertext E-value; includes structured E5 secret keys |
| Smaller public probes preserve matching | machine-checked | `partial_key_match_transfer` | Arbitrary frames, both ciphertext values and a smaller public key recipe |
| Coherent ciphertext assemblies preserve matching | machine-checked | `General.assembly_partial_key_match_swap` | Actual initial frames, source coherence and probes below the decryption size |
| Minimum partial-key decryptions stay stuck | machine-checked | `General.minimum_partial_key_decryption_failure` | Source minimum and partial-key/ciphertext E-values; origins derived |
| The partial-key/ciphertext equality branch transfers both ways | machine-checked | `General.minimum_partial_key_decryption_equality_swap` | Two source minima and their source argument values; bounded hypothesis retained |
| Full static equivalence | conjectured | Open task | Other value classes, arbitrary-recipe closure and final frames remain required |

## Controls and executable scope

[DecryptionProbeSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/DecryptionProbeSPOT.lean)
contains eight public theorem controls. A structured secret key actually takes
E5 and reaches name 90, refuting omission of the direct alternative. A correct
inner key with a nonce-51 binding cannot decrypt nonce-50 ciphertext, refuting
omission of complete binding. Reducible key, ciphertext and outer partial-key
wrappers produce actual matching paths and the independently specified name-90
plaintext.

A changed published binding enables E6 in a separate frame fixture. Comparing
the binding handle with the ciphertext handle detects the change below the
budget, demonstrating the role of the bounded premise. In actual initial frames,
a partial key made from public names applied to the first honest ciphertext is
an exact six-node minimum for arbitrary valid candidate assignments. Two such
minima with different binding names instantiate the two-sided equality theorem
and remain unequal. A reducible supplied partial-key target exercises failure
transfer. A coherent, fully public ciphertext assembly with a structured secret
key exercises positive match transfer, ruling out universal rejection.

`DecryptionProbeExperiments.lean` first detects both known defects at input 0,
seed 1, zero shrinks. The omitted-binding fixture is selected by internal fixture
index 4. The positive matching formula and strict probe-size checks pass seeds
1, 7 and 42, each with 500 configured cases, size 40 and `gaveUp=0`, followed by
512 deterministic inputs for both checks. Matching fixtures vary direct
structured-key E5, ordinary E6, a wrong key, a changed binding nonce and reducible
arguments. Size fixtures vary recipe-chain lengths. The tightened bound `|r|`
passes the gate before the strengthened proof is checked.

These are raw-normalization families, not a full-E decision procedure or a
privacy proof. Full-E matching, minimum size and transfer have separate kernel
proofs. Diagonal candidate assignments supply the bounded premise in transfer
controls; different-vote static equivalence is not assumed.

## Reproduction and remaining work

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/DecryptionProbeExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
python3 scripts/check_helios_claims.py
```

The full build passes (3499 jobs), including 15 new public theorem type/axiom
audits. Its 1324 nonempty axiom reports use only `propext`, `Classical.choice` and
`Quot.sound`; another 17 reports are axiom-free. No warnings, errors or `sorryAx`
occur. The local log is `tmp/variable-overlap/decryption-probe-full-build.log`.
The source checker covers 355 public theorem audit entries and selected stale
claims in 21 current-status documents. It does not replace elaboration or prove
log freshness.

Trusted definitions remain E/E0, actual matching paths, public recipes,
node-count minima, the general initial frames and the existing ciphertext
assembly and minimum-origin results. The independent reality oracle is the
source's unsorted E5 rule and E6's complete ciphertext binding, recorded in the
[symbolic model](helios-symbolic.md). No equation, public operation, custom axiom
or assumed confluence changed.

The subsequent [value-shape results](helios-value-shapes.md) discharge the source
argument-shape premises and complete the minimum stuck-decryption and stuck-
projection equality branches in both directions. Arithmetic values, arbitrary
nonminimum evaluation transport and the global smaller-observation premise
remain open. Final frames publishing
partial decryptions and historical process matching remain required. See the
preceding [stuck-destructor record](helios-stuck-destructors.md),
[static-equivalence interfaces](helios-static-equivalence.md) and canonical
[task list](../../task%20list.md).
