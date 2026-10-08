# Historical symbolic repair

Status: the term/frame foundations and controls below are machine-checked;
the full privacy theorem remains conjectured.
The user selected this phase before the concrete cryptographic repair, and
authorised the [documented tuple-termination correction](helios-symbolic-tuple-guard.md).
The corrected termination predicate is part of the target; the printed predicate
is retained as a counterexample control.

## Research enquiry

Goal: reproduce Cortier–Smyth Theorem 1 under its historical symbolic semantics.
Candidate claim: for the documented correction, every positive candidate count and at least two voters,
swapping the two honest candidate substitutions yields labelled bisimilar
processes under component weeding. Falsifiers include an accepted ballot whose
contribution depends on an honest choice, a public recipe equality that differs
between worlds, or an unmatched observable transition. The formal oracle must
ultimately check all three obligations, not merely equality of final tallies.
The reality oracle is the author preprint §§5.1–5.3, Figures 2–5 and Appendix B.

## First increment: terms and observations

The first proof obligations are substitution stability of equality modulo E,
closure of public observations under that equality, the source's aggregate
proof example, and symmetry of the two honest contributions to a tally.
A mutation dropping commutativity would prevent the swap derivation; accepting
only a fixed finite recipe family would fail to express the source theorem.

`ExplainableCrypto.Helios.Symbolic` uses unbounded inductive terms. It includes
four constants, unary `fst`, `snd`, `pk`, binary `pair`, ciphertext product,
plaintext sum, nonce composition, `partial`, `dec`, ternary `penc`, `checkspk`,
and quaternary `spk`. The printed signature list in §5.2.1 omits `pk` even though
E5/E6 and the process use it; the formal signature includes that unary symbol.
Names and substitution variables are distinct constructors. Fixed constructor
arities prevent malformed applications.

Equality modulo E is the equivalence/congruence closure of E1–E9 and the three
associativity/commutativity laws. It is a Lean inductive proposition, not a Lean
axiom or an assumed convergent evaluator. In particular, E3 and E4 do not assert
that `zero` is an identity on arbitrary terms. There is no ciphertext identity,
nonce identity, inverse, proof destructor, or concrete group equation.

Frames contain a finite set of restricted names and a fixed number of public
handles, each bound to a closed term. Recipes can apply every public function
and refer to handles; they may not name a restricted atom. Static equivalence
quantifies over every pair of permitted recipes and compares equality modulo E
after substitution. No private key or randomness is available merely because
Lean can inspect a term constructor.

## Remaining source obligations

The full theorem needs confluence modulo E0 (or another proved
characterisation of equality); [termination and normal-form existence](helios-rewriting.md)
are now checked. The [conditional confluence framework and triple overlap](helios-confluence.md)
are also checked, with the full local-confluence premise still open. It also needs the accepted-ballot lemma, static equivalence of
honest ballot frames and final partial-decryption frames, and a labelled
transition relation with a bisimulation proof. The existing finite experiments
are controls and historical attack witnesses, not substitutes for these lemmas.
A separating algebra for E now proves that `zero`, `one` and `one + one`
retain the distinctions used by the controls. It supplies neither a complete
equality decision procedure nor normal forms. No remaining obligation is
introduced as an axiom to close the privacy statement.

## Checked foundation ledger

All names below are in `ExplainableCrypto.Helios.Symbolic`.

| Claim | Status | Declaration | Limit |
| --- | --- | --- | --- |
| E is stable under substitution | Machine-checked | `Equation.subst`, `EqE.subst` | The explicitly encoded E |
| Recipe interpretation respects E | Machine-checked | `Term.subst_congr` | Pointwise equationally equal handle values |
| Public computation preserves static equivalence | Machine-checked | `Frame.StaticEq.derive` | Same restricted-name set and handle domain in both input frames; arbitrary finite output domain |
| E does not collapse zero, one and two | Machine-checked | `zero_not_one`, `two_not_one`, `EqE.denote` | Sound separating algebra, not a complete normaliser |
| Aggregate proof verifies after permutation | Machine-checked | `aggregate_example`, `aggregate_permutation` | The source Example 1 with plaintexts zero/one and arbitrary key/nonces |
| Partial decryption reveals the associated plaintext | Machine-checked | `partial_decryption_observable` | E6, not a distributed decryption implementation |
| Honest contribution swap preserves the tally term | Machine-checked | `honest_tally_swap` | Any list of identical further contributions in both worlds; their independence still needs proof |
| Public observations are neither always equal nor raw syntactic equality | Machine-checked | `published_bit_distinguishable`, `reduced_bit_staticEq` | Small proof-oriented controls |
| Recipes may copy handles but may not name secrets | Machine-checked | `replay_recipe_allowed`, `secret_name_forbidden`, `public_handle_allowed` | Definition of public recipes |

The separating interpretation uses natural numbers: the three AC operations
map to addition, pairs use the injective natural-number pairing, bottom maps to 2 (so its first projection can be separated from itself),
and encryption maps to its plaintext interpretation. The last choice is permissible for a
mathematical model of the equations but would be wrong as an attacker evaluator.
It is used only to prove that an E-equality would imply equal interpretations,
and hence to refute particular E-equalities. Static equivalence uses E directly.

Reproduce with `lake build` or
`lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`. The audit checks
all public theorem types and kernel-reported axioms. These structural induction
proofs and literal controls do not claim a randomized search over E-equality,
which does not yet have a proved decision procedure. The existing finite-model
Plausible campaigns remain in the main build. The [rewriting refutation gate](helios-rewriting.md) has run for termination
and raw root matching. Further gates remain necessary for confluence and
the accepted-ballot proof.

Validation after the documented correction: `lake build` passes (3277 jobs).
The symbolic audit reports only subsets of `propext`, `Classical.choice` and
`Quot.sound`, with no `sorryAx` or custom axioms. The original mutation/OTP
proof bodies are unchanged apart from namespace and path replacements.
