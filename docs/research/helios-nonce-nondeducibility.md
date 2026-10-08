# Protected-name non-deducibility

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: machine-checked non-deducibility of individual restricted names and
composition terms containing a restricted-name factor, for frames satisfying an
explicit protection invariant. Both results quantify over every public recipe.
They support the nonce arguments in Cortier–Smyth Appendix B.3, Lemma 9.
The [parametrized initial historical frames](helios-historical-frames.md) now
instantiate these results. The [minimum-recipe structure](helios-minimal-recipes.md#minimum-historical-origins-and-destructor-composition)
is checked. The [general candidate frames](helios-candidate-substitutions.md)
now support all valid ground candidates and complete Lemma 9 with the authorised
tail guard. Their raw values may fail syntactic protection; the general proof
transports each public recipe to an E-equal protected value.

## Protection invariant

`Term.nonceSafe restricted t` checks that restricted names occur only in
positions from which the encoded rules cannot expose them: beneath pk or spk,
or in the randomness argument of penc. It checks both the key and plaintext
arguments of penc, and all arguments of every other constructor.
The definition is a metatheoretic predicate, not an extra public operation.
It is sufficient protection, not a characterization of all non-deducible frames.

E0 preserves the Boolean exactly. Oriented contextual reductions preserve its
truth forward. Arbitrary full-E expansion does not preserve it: one is E-equal
to fst(pair(one, restrictedName)), whose discarded field violates the invariant.
Ignoring ciphertext plaintext is also unsound: known-key decryption exposes it.
Both failures are retained as checked controls.

## Public statements

All declarations are in `ExplainableCrypto.Helios.Symbolic`.

| Claim | Declaration | Premises and scope |
| --- | --- | --- |
| E0 preserves protection | `BaseEq.nonce_safe` | Arbitrary terms |
| Oriented paths preserve protection | `ReducesModulo.nonce_safe` | Protected source; forward direction |
| Public syntax is protected | `Term.Public.nonce_safe` | Same restricted-name set |
| Substitution preserves protection | `Term.nonce_safe_subst` | Protected input and every substituted value |
| A protected term cannot equal a restricted name | `nonce_safe_not_eqE_name` | Source protection and name membership |
| Public recipes cannot deduce restricted names | `Frame.nonce_not_deducible` | Every handle protected, recipe public, name restricted |

The non-deducibility proof uses confluence to obtain a common reduct with the
claimed name. Name irreducibility turns that path into E0 equality. The reduct
is protected by forward preservation, contradicting the name's restriction.
The frame theorem adds public-recipe substitution to this argument. No failed
search, assumed confluence or custom cryptographic axiom is used.

## Controls and validation

The example frame exposes a key, encrypted bit, proof and one-candidate tuple.
`published_nonce_not_deducible` ranges over all its public recipes. Separate
controls project its ciphertext and decrypt the public bit with a known key.
Thus useful public computation is still possible. Leaking a name through a
handle refutes dropping the frame premise; using a nonpublic literal name
refutes dropping the recipe premise. Plaintext leakage and reversed projection
refute two tempting but incorrect protection invariants.

The executable gate passes seeds 1, 7 and 42 (500 configured cases per seed,
maximum size 40, `gaveUp=0`) and all 256 deterministic inputs. Both deliberate
negative properties fail at n=0, seed 1, zero shrinks. It checks generated raw
reductions and directed rule fixtures; the general proof covers arbitrary
modulo paths and recipes.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/NonceProtectionExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
Validation: 3361 jobs pass, with 545 axiom reports containing only `propext`,
`Classical.choice` and `Quot.sound`. The final log has no warnings, errors or
`sorryAx`.

The [general reconstruction](helios-candidate-substitutions.md) applies validity
and weeding to the checked minimum forms, completing Lemma 9. The individual-name theorem does not establish
static equivalence, ballot secrecy or privacy of arbitrary frames.


## Compositions containing restricted names

`ComposedNonce.lean` extends exclusion to any target with a restricted-name E0
class among its outer composition factors. An arbitrary modulo step cannot
select that name factor because it is irreducible; the factor remains in the
remainder. Protection excludes such a factor from the recipe's common reduct.
Other factors may reduce, expand or contract; target irreducibility is unnecessary.

| Claim | Declaration | Scope |
| --- | --- | --- |
| A name factor survives one step | `ModuloStep.compose_name_mem` | Exact E0 class membership among outer composition factors |
| A name factor survives all paths | `ReducesModulo.compose_name_mem` | Includes E0-only endpoint changes |
| Protected terms have no restricted name factor | `Term.nonce_safe_no_name_factor` | Protection and restricted-name membership |
| Protected terms cannot equal such a target | `nonce_safe_not_eqE_name_factor` | Arbitrary, possibly reducible target |
| Public recipes cannot deduce such a target | `Frame.composed_nonce_not_deducible` | Protected handles, public recipe and target factor witness |
| Public recipes cannot deduce name ◦ rest | `Frame.nonce_with_remainder_not_deducible` | Any ground remainder |

The gate checks generated raw composition terms, repeated name occurrences and
expanding projection factors. Seeds 1, 7 and 42 pass (500 configured cases,
maximum size 40, `gaveUp=0`), as do 256 deterministic inputs. The false claim
that arbitrary syntactic name occurrences persist fails at n=0, seed 1,
zero shrinks. A checked projection discards the named pair member. The stronger
raw-count test is finite evidence; the general theorem asserts membership.

Checked controls quantify over all public recipes of the published fixture and
arbitrary remainders, include permuted repeated factors, and retain a reducible
target whose factor count grows from three to four. The restricted name persists
through that actual step. Public ciphertext projection still works: a nonce
inside ciphertext randomness is not an exposed composition factor.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/ComposedNonceExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
Validation: 3364 jobs pass with 558 axiom reports containing only `propext`,
`Classical.choice` and `Quot.sound`; no warnings, errors or `sorryAx` appear.
The protection premise remains substantive; the initial historical-frame
instantiation is recorded separately. Minimum-recipe structure is now checked;
the [general reconstruction](helios-candidate-substitutions.md) completes Lemma 9.
Static equivalence and privacy remain open.
