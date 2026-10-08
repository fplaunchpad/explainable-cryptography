# Public-key-valued equality observations

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: machine-checked. Every minimum public recipe with a pk-constructor value
in the actual initial frame is either an explicit pk constructor or the
published election-key handle. The public-key-valued minimum-recipe branch
transfers equality from the same explicit smaller-observation premise used by
the [ciphertext](helios-ciphertext-observations.md) and
[proof](helios-proof-observations.md) branches. The global premise and full
static equivalence remain open.

The result covers all positive candidate counts, both swaps and arbitrary valid
ground candidate representatives. This branch does not need nonce freshness.
The full secret-name restriction remains explicit where it excludes public
reconstruction of the election key.

## Reachable paths and exact origins

[PublicKeyOrigins.lean](../../ExplainableCrypto/Helios/Symbolic/PublicKeyOrigins.lean)
first accounts for key-valued destructor results. `EqE.projection_pk_inversion`
proves that a fst/snd projection E-equal to a public key reaches an argument pair
and selects a key-valued member. The original argument need not be a literal
pair. `EqE.decryption_pk_inversion` proves that a key-valued decryption reaches
an actual E5 or E6 match. Both statements permit arbitrary reducible target-key
arguments and retain the reachable match in their conclusions.

A tuple is never E-equal to a pk-constructor term, including its empty suffix.
`ProjectionChain.not_pk_of_tuple` extends this to every fst/snd chain over a
tuple whose fields are neither pair-valued nor key-valued. Historical ballot
fields satisfy those conditions: they are ciphertexts, component proofs and
an aggregate proof. Their public-key arguments cannot be extracted by tuple
projection.

`Historical.General.frame_projection_pk_origin` therefore identifies the only
key-valued projection chain over any of the three initial handles: the key
handle itself, `var 0`. All nontrivial chains over that key handle are stuck
before reaching another pair, and ballot chains expose no key-valued field.
No caller minimum-size premise is needed for this chain theorem.

[PublicKeyObservationInduction.lean](../../ExplainableCrypto/Helios/Symbolic/PublicKeyObservationInduction.lean)
uses these paths and existing minimum pair/ciphertext origins to prove
`minimum_public_key_form`. Minimum projections cannot be raw projections of a
constructed pair; the remaining chain case would have to be `var 0` and cannot
retain a projection head. Minimum decryption cannot reach a matching ciphertext
whose plaintext has a smaller public recipe. Other heads are excluded by
full-E constructor separation. The resulting `PublicKeyRecipeForm` is exactly:

```text
r = var 0, or r = pk(a) for some recipe a
```

This origin theorem retains the caller's arbitrary name policy. Its supplied
pk value may have a reducible argument. It does not classify arbitrary
nonminimum wrappers by their original syntax.

## Election-key separation and equality transfer

`frame_secret_key_not_deducible` instantiates protected-value non-deducibility
at the trustee secret-key name under `Names.restricted`. Full-E pk injectivity
then gives `constructed_key_not_election_key`: no pk constructed from a full-
policy public argument recipe equals the election public key.

The full policy is essential to that general constructor-separation argument.
The nonce-only policy permits the literal trustee secret-key argument when it
is distinct from the honest nonces. Its pk is then equal to the published key.
That recipe is not minimum, since the published handle is smaller; the control
does not claim to refute the final minimum theorem under a weaker policy.

The four exact form comparisons are:

| Left/right forms | Equality test |
| --- | --- |
| Published handle / published handle | true |
| Constructed key / published handle | false under the full name policy |
| Published handle / constructed key | false under the full name policy |
| Constructed key / constructed key | Equality of the two argument recipes |

The last comparison is strictly smaller in the sum of original recipe node
counts. `public_key_form_equality_swap` transfers it through
`Frame.ObservationsBelow`; no pointwise key-value preservation is required.
`minimum_election_key_handle` also identifies `var 0` as the only minimum
full-policy recipe for the exact election key.

`minimum_public_key_equality_swap` takes two first-world minimum full-policy
recipes and a supplied pk-constructor value for each. It derives both forms and
transfers equality under `ObservationsBelow` at the sum of the two original
sizes. It assumes no form certificate, second-world value or preserved minimum
syntax. No freshness premise is needed for this branch, although the complete
static-equivalence objective retains freshness for its other cases.

## Claim ledger

All names below are under `ExplainableCrypto.Helios.Symbolic`; `General`
abbreviates `Historical.General`.

| Claim | Evidence | Declaration | Scope |
| --- | --- | --- | --- |
| Key-valued projection reaches a pair selection | machine-checked | `EqE.projection_pk_inversion` | fst/snd only, full-E target, actual argument path |
| Key-valued decryption reaches an E5/E6 match | machine-checked | `EqE.decryption_pk_inversion` | Arbitrary reducible arguments and pk target |
| Ballot chains expose no public-key constructor | machine-checked | `General.voter_projection_not_pk` | Actual fields, every chain and valid candidate assignment |
| A key-valued chain is the published key handle | machine-checked | `General.frame_projection_pk_origin` | All three initial handles; no minimum premise |
| Minimum key-valued syntax has two forms | machine-checked | `General.minimum_public_key_form` | Arbitrary caller policy and first-world pk value |
| A public constructor cannot reproduce the election key | machine-checked | `General.constructed_key_not_election_key` | Full secret-name policy; no minimum or freshness premise |
| The election key's minimum full-policy recipe is its handle | machine-checked | `General.minimum_election_key_handle` | Minimum recipe and exact election-key value |
| Minimum public-key equality transfers from smaller tests | machine-checked | `General.minimum_public_key_equality_swap` | First-world minima/values and explicit bounded hypothesis |

## Independent controls

[PublicKeyObservationSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/PublicKeyObservationSPOT.lean)
contains eight checked controls. The published key is an actual one-node
minimum. A key constructed from public name 40 is an exact two-node minimum;
its proof excludes every size-one competitor, including unbounded names and
all three handles, for arbitrary valid candidate assignments in the fixture.

A projection wrapper around the published handle is public and has the same
key value, but is neither one of the exact forms nor minimum. This retains the
counterexample to omitting minimum size. A nonce-only-policy recipe naming
secret key 10 reproduces the election key and fails the full policy.

The path controls fix the output independently as `pk(40)`. They check a pair
revealed by a projection, a projected E5 key and a projected E6 partial-decryption
value, then instantiate the path-inversion conclusions. Another control rules
out extracting a key by projecting an honest ciphertext field.

A reducible public argument preserves its constructed key value, while public
names 40 and 41 give unequal keys. Finally, the complete minimum-key induction
interface is instantiated with a one-node handle and a two-node constructed
key, whose total size is three and whose values are unequal. Identical honest
candidate assignments make the smaller-test hypothesis available for every
bound without assuming different-vote static equivalence.

## Executable scope and validation

`PublicKeyObservationExperiments.lean` checks actual general-frame fst/snd
chains and public key constructions. The omitted-minimum mutation fails at
generated input 0, seed 1, with zero shrinks: a projection wrapper has a key
value outside the two syntactic forms.

Both positive gates pass seeds 1, 7 and 42, each with 500 configured cases,
maximum size 40 and `gaveUp=0`, plus 256 deterministic inputs. A separate
2400-input chain sweep covers all three roots and all fst/snd words of lengths
zero through four, at one through five candidates and both swaps. Shorter
chains recur in this encoding; 2400 does not count distinct chains. Candidate
assignments in this gate are fixed to left abstention and right selection of
candidate zero. The theorem and controls cover the broader candidate scope.

The constructor gate compares a fresh public-name argument with a reducible
projection wrapper and separates both from the election key. The executable
checks use raw normalization and constructor shape/equality on these families;
they are not a full-E equality decision procedure or proof of all-recipe privacy.

Reproduce with:

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/PublicKeyObservationExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
python3 scripts/check_helios_claims.py
```

The full build passes (3474 jobs), including 22 new public theorem type/axiom
audits and five definition checks. Its 1214 nonempty axiom reports use only
`propext`, `Classical.choice` and `Quot.sound`; 17 additional reports are axiom-free.
There are no warnings, errors or `sorryAx`. The local log is
`tmp/variable-overlap/public-key-full-build.log`. The source audit checks
245 public theorem entries and selected stale claims in 15 current-status
documents; it does not replace elaboration or establish log freshness.

Trusted definitions remain E/E0, tuple projections, pk injectivity, public
recipes, general frames and protected-name semantics. The reality oracle is
the source frame's published `pk(skT)` handle, restricted `skT`, and opaque
ciphertext/proof constructor arguments. No equation, public operation, custom
axiom or confluence assumption changed.

The subsequent [initial-frame partial-decryption branch](helios-partial-decryption-observations.md)
now derives its constructor origins and transfers both ordered field tests.
Remaining work includes other value heads and transport of arbitrary recipe
evaluations to establish the global smaller-observation premise. Final partial-
decryption frames and historical process matching also remain open. Preserve
the complete objective in the canonical [task list](../../task%20list.md).
