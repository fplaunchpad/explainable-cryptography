# Historical symbolic repair

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

[Historical process stages](helios-process-stages.md) now have checked
reachable-state invariants, same-label transition matching in both directions,
and static equivalence at every reached public domain. The twelve-stage model
allows arbitrary public input recipes, stops on rejection, and requires every
eligible input before publication. Ten controls include completed zero/two-input
elections, replay rejection and tally two. The next B9 obligation is operational
correspondence with the source applied-pi processes, including substitutions,
private messages, structural rules and fresh binders. B9/B10 remain open;
coverage stays 8/10 (80%, unweighted).

B8 is complete. [Published transcript static equivalence](helios-published-static-equivalence.md)
proves all public equality observations for the actual partial and final frames,
including arbitrary nesting of trustee-partial and result handles. Freshness,
valid ground candidates, public initial-handle submissions and their sequential
acceptance are explicit; no local-transport or static-equivalence callback remains.
All twelve expanded operator cases are closed. The next milestone is B9:
process transitions, adaptive-recipe flattening and matching. B10 labelled
bisimilarity and the full symbolic secrecy theorem remain open. Coverage is
8/10 unweighted milestones (80%), not an effort estimate.

The maintained [proof blueprint](helios-proof-blueprint.md) records dependencies
and the completion condition. Earlier checkpoint narratives below retain their
historical scope; their former B7/B8 assumptions are now discharged.

Status: the term/frame foundations and controls below are machine-checked;
the full privacy theorem remains conjectured.
The user selected this phase before the concrete cryptographic repair, and
authorised the [documented tuple-termination correction](helios-symbolic-tuple-guard.md).
The corrected termination predicate is part of the target; the printed predicate
is retained as a counterexample control.


The [minimum-transport criterion](helios-minimum-transport.md) closes the
generic total-size induction with explicit shared representatives. The
[complete observation assembly](helios-observation-assembly.md) now proves
forward equality preservation for every minimum pair under smaller tests.
Reverse shared minimization supplies destination minima and closes the reverse
step. Initial-frame static equivalence is therefore equivalent to shared
minimization in both directions. Local root minimization with minimum children
is the remaining sufficient proof target in both orientations. A checked
nine-versus-eight-node counterexample still prevents assuming that child
minimization fits the original observation bound.


The [local-root closure](helios-local-root-transport.md) now proves that minimum
children give minimum parents for constructed keys, partial constructors,
proofs and semantically stuck destructors. These roots are their own shared
representatives. The remaining transport interface requires new witnesses only
for nonminimum roots with minimum children: successful destructors, pairs,
ciphertext constructors and arithmetic. The subsequent projection theorem below
discharges fst/snd. Pairing and ciphertext construction are discharged by the
subsequent results below, which also close composition, addition and
multiplication. Successful decryption/checking remain open in both swaps.


The [complete projection result](helios-complete-projections.md) now supplies
shared minima for every fst/snd with a minimum child, without an observation
premise. Exact honest ciphertext-selector minima close all nonempty ballot-tail
minima. The empty tail uses bottom; the one-candidate aggregate retains its
shorter component representative.

The [pair transport result](helios-pair-transport.md) now supplies shared minima
for pairs with minimum children. Exact nonempty-tail origins and matching
transfer for every honest field/tail preserve the shorter tail representative
across assignments.

The [ciphertext constructor result](helios-ciphertext-constructor-minima.md)
proves that penc with minimum children is itself minimum in the initial frame,
without freshness or an observation premise. The selected key and grouped
components fit the original recipe bound; a public nonce excludes honest and
mixed groups.

The [composition minimum result](helios-composition-minima.md) now proves that
compose with minimum children is minimum, under any caller name policy in the
initial frame. Equal semantic factor bags preserve minimum leaf costs and
occurrence counts. No freshness or observation premise is needed for this
closure.

The [addition minimum result](helios-addition-minima.md) supplies a raw-E0-equal
source-minimum representative for addition with minimum children. Exact atom
costs and optional numeric counts establish global minimality; raw E0 equality
preserves evaluation in every destination frame. The three remaining local
cases are successful decryption, successful proof checking and multiplication
in both orientations. Those cases and full static equivalence remain open.

The [multiplication partition minimum criterion](helios-multiplication-minima.md)
now proves global source minimality when a normal endpoint's partition pieces
are minimum. Two minimum groups whose single-factor representatives form a
normal product are covered. Source normal partitions require no observation
premise, but their fused groups need not be minimum.

[Shared-piece reassembly](helios-multiplication-reassembly.md) now constructs a
globally minimum representative with both frame equalities. Well-founded
recipe-size induction discharges non-ciphertext products using strictly smaller
partition pieces. That earlier criterion retains successful decryption,
successful checking and whole-ciphertext products in both swaps. Shared minima
for arbitrary whole-ciphertext products are narrowed further by the next result.

The [honest-only product result](helios-honest-product-minima.md) now proves
that every nonempty combination of fresh honest selectors is globally minimum.
Minimum competitors must retain exactly the same indexed occurrence bag and
therefore the same cost. These products are already shared in every destination.
Nonminimum ciphertext products have a constructed or mixed public group.
[Constructed-only compression](helios-constructed-compression.md) gives a
strictly smaller single-constructor representative for a nontrivial coherent
constructed group; minimum public-nonce ciphertexts have raw constructor syntax.

[Simultaneous minimum transport](helios-joint-minimum-transport.md) now derives
bounded observations from two-way smaller shared minima at the same bound and
supplies those hypotheses by unbounded recipe induction. Constructed-only
products are discharged inside that criterion. The
[mixed compression result](helios-mixed-compression.md) discharges two or more
public constructors and classifies every minimum mixed competitor.

[Initial-frame static equivalence](helios-initial-static-equivalence.md) is
now proved by `Historical.General.initial_frame_staticEq`, for every pair of
public recipes, fresh names and valid ground candidate substitutions. All
local transport premises are discharged. **B7 is complete: twelve of twelve
operators and seven of ten top-level milestones**. The blueprint moves to
**B8, accepted adversarial ballots and final transcript equivalence**. Final
partial-decryption frames, historical process matching and full secrecy remain
unproved. The preceding transport interfaces describe the proof's earlier
stages; the new initial theorem now supplies their static-equivalence premise.

[Sequential acceptance and shared tallies](helios-shared-tallies.md) now
instantiate that initial theorem for any finite accepted public submission
sequence. Each accepted ballot is appended before the next is checked. One
aligned list of valid bit vectors explains all submissions in both worlds;
`accepted_sequence_tally_numeric` proves the same actual E6 result as a numeral
bounded by the voter count. This closes the source Lemma 11 tally obligation.
The current B8 frontier is the full final-frame theorem with published partial
decryptions; top-level coverage remains seven of ten milestones.

[Actual published frames](helios-published-frames.md) now preserve the initial
three handles, append the complete partial tuple, then append the result tuple.
`final_frame_staticEq_iff_partial` reduces final equivalence exactly to the
partial frame, using a checked public recipe for the actual results. The
aggregate-partial frame equivalence remains unproved. A checked counterexample
shows that publishing an individual-ballot partial can leak its vote despite
equal totals. That control does not attack the defined aggregate publication.

[Trustee-partial boundary theorems](helios-trustee-partial-boundary.md) now
characterize every match against an initial public recipe by full aggregate
binding equality. For accepted sequences these matches transfer across the
swap and actual successful probes return a shared bounded numeral. Equalities
among partial slots also transfer. The theorem excludes partial-keyed
ciphertexts only in the initial frame; a checked public recipe constructs and
decrypts one after publication using E5. Arbitrary nested new-frame recipes
remain the B8 obligation.

[Published-frame name protection](helios-published-protection.md) now covers
arbitrary nested public recipes in the actual partial frame and, for public
submissions, the final frame. An E-valued invariant treats partial fields as
opaque while preserving ciphertext plaintext checks and both decryption rules.
It excludes restricted names, composed name factors, constructed election keys
and constructed trustee partials. It supplies name-separation premises for the
extended recipe classification, without proving that classification or all
cross-world equality observations.

[Individual published handles](helios-expanded-published-frames.md) now provide
an exactly equivalent presentation of the actual final frame, by public
projection and complete tuple reconstruction. Published values have one-node
minimum representatives. Minimum recipes for published trustee partials are
partial-slot handles in accepted elections, and bound tally decryptions have
shorter result-handle recipes. The remaining B8 proof can use this presentation
and return through the exact static-equivalence iff; minimum syntax costs do
not transfer across that change.

[Expanded value origins](helios-expanded-value-origins.md) now reuse the existing
ciphertext-product certificates to prove pair/ciphertext origins and rule out
successful E5/E6 in a whole minimum decryption. Partial-valued minimum recipes
are constructed partials or individual published slots. The partial-equality
matrix transfers under smaller observations, and constructed partials with
minimum children are minimum. Accepted public elections supply the numeric
result values required by these origin proofs. Other value branches and the
global expanded-frame observation induction remain open.

[Expanded public keys](helios-expanded-public-keys.md) now have exact minimum
origins: the retained election-key handle or explicit key constructors.
Published-frame name protection excludes mixed aliases. Minimum public
arguments give minimum key constructors, and their full equality matrix
transfers under smaller argument observations. Actual accepted elections
supply the numeric-result premise; initial and expanded frames reuse one
structural origin proof. Other value branches and the global expanded-frame
induction remain open.

[Expanded proof values](helios-expanded-proof-values.md) now have exact
minimum constructed/borrowed forms. Public nonce recipes using new handles
cannot recover honest component nonces or aggregate nonce factors. Minimum
arguments give minimum proof constructors. All four constructed argument
comparisons use smaller observations, while honest proof comparisons reuse
B7 through old-handle embeddings. The general observation induction remains
open; this proof branch does not establish final-frame equivalence.

[Expanded pair values](helios-expanded-pair-values.md) now have exact
minimum constructed/nonempty-tail forms and pair-valuedness in either world.
The equality matrix uses smaller tests of both projections when either side
is constructed, and reuses retained tail identity for two borrowed sides.
Empty tails and invalid eta on partials remain explicit controls. Pair-root
shared minimum transport and the global observation induction remain open;
minimum children alone do not imply minimum pairing.

[Expanded atomic values](helios-expanded-atomic-values.md) now include both
literal constants and constant-valued result handles. Minimum names remain
literal. Accepted numeric/shared tally values supply atomic value and equality
transport with no smaller-observation premise. The result is full-E equality,
not raw literal evaluation; a checked `0 + 0` raw result preserves that
boundary. Other value branches and the global induction remain open.

[Expanded check values](helios-expanded-check-values.md) now derive exact
stuck-check syntax. Successful minimum projections still select old honest
data, and stuck checks of minimum children are minimum. The equality branch
reuses smaller whole-check/ok probes to preserve failure, then compares three
ordered arguments. The global smaller-test premise remains open; value-shape
reflection and both stuck-destructor branches are checked below.

[Expanded ciphertext keys](helios-expanded-ciphertext-keys.md) now supply a
strictly smaller public key recipe and forward ciphertext-value transport.
The generic induction reuses existing ciphertext syntax, full-E inversion and
the homomorphic law; actual expanded selectors discharge its leaf premise.
Accepted minimum recipes need only the remaining smaller-observation premise
for this transfer. The result-handle argument below supplies E6 failure
transport at the bound needed for syntactic decryption equality. Conditional ciphertext equality is checked in the
[assembly theorem](helios-expanded-ciphertext-assemblies.md); global shared-minimum
induction remains open.

[Expanded value shapes](helios-expanded-value-shapes.md) now preserve pair,
ciphertext and partial-decryption value classes in both directions for source
minimum recipes under strict smaller observations. Accepted-election premises
supply numeric results in both worlds. The decryption case retains E5 and full
E6 binding: any remaining destination match is a borrowed trustee E6 result,
which is numeric and cannot have those three data shapes. This closes shape
reflection at the original recipe-only bound. A separate whole-decryption/
result-handle probe excludes destination success with an explicit two-node
allowance; the ordinary combined-size bound for two minimum decryptions pays
for both probes, closing their syntactic equality branch. Exact origins and
arbitrary stuck-value equality are checked below; global induction remains
open. The shared structural induction also serves the existing initial-frame theorem.

[Expanded stuck values](helios-expanded-stuck-values.md) now supply exact
projection/decryption origins and minimum closure under source failure.
Accepted arbitrary minimum recipes with stuck values preserve equality under
strictly smaller observations; pair-shape reflection supplies destination
projection failure, and the checked result probes supply E5/E6 failure within
the decryption comparison bound. A shared origin helper preserves the initial
proof's public statements. Remaining value branches and global shared-minimum/
observation induction are still open.

[Expanded composition](helios-expanded-composition.md) now has exact source
and destination origins, semantic leaf atoms in both worlds, full-E factor
comparison and minimum closure. The after-swap origin argument uses numeric
E6 output exclusion at the recipe-only observation bound; it does not assume
that all destination decryptions fail. Existing factor bags and exact leaf
costs retain multiplicity. Multiplication shared minimum transport,
shared minimum transport and global observation induction remain open.

[Expanded addition](helios-expanded-addition.md) now includes published result
handles in its exact minimum origin forms. Accepted shared numerals give a
handle-aware addition summary preserving atom multiplicity and optional zero.
The conditional full-E equality branch uses strictly smaller leaves to pay for
destination result probes within the original recipe-size bound. The
[minimum representative result](helios-expanded-addition-minima.md) now closes
addition shared minimum transport; the original sum need not itself be minimum.
Multiplication shared minimum transport,
remaining shared minima and the global expanded-frame induction remain open.

[Expanded addition minima](helios-expanded-addition-minima.md) now close the
addition shared-minimum obligation. A least attainable numeric cost accounts
for one-node published numerals; exact summary realization and minimum-leaf
cost equality prove global source minimality against all public recipes.
Accepted common tally values make the representative equal in both frames,
with no smaller-observation premise. Multiplication shared minimum transport,
remaining shared minima, successful-case integration and the global B8
induction remain open.

[Expanded multiplication](helios-expanded-multiplication.md) now closes the
conditional non-ciphertext product-equality branch. Exact normal-product
origins allow numeric E6 success, and existing fusion partitions supply strictly
smaller public group recipes in both worlds. The argument preserves all factor
occurrences and requires no destination minimum premise. Multiplication shared minimum transport, other shared minima,
successful-case integration and the global expanded-frame induction remain open.

[Expanded ciphertext groups](helios-expanded-ciphertext-groups.md) now have
an exact constructed/honest/mixed comparison matrix over all published handles.
Opaque nonce-factor separation preserves honest occurrence bags and the public
remainder; mixed payload tests retain zero padding. Existing group merge laws
and bounded observation transfer now work at any handle count. The key equality
remains explicit. The [expanded assembly theorem](helios-expanded-ciphertext-assemblies.md)
now derives exact syntax, original recipe-size bounds and conditional minimum
ciphertext equality. Multiplication shared minima and global B8 induction remain open.

[Expanded ciphertext assemblies](helios-expanded-ciphertext-assemblies.md)
now connect the group matrix to actual source minimum ciphertext recipes.
Exact syntax, selected-key publicness/strict size, original group bounds and
common-key agreement in both frames are derived. The final comparison iff
retains only the source minima, accepted-election premises and strictly smaller
public observations. Multiplication shared minimum transport and the global
observation induction remain the next integration work.

[Expanded observation assembly](helios-expanded-observation-assembly.md)
now combines all twelve normal operator heads plus names and constants into
forward minimum equality preservation. Reversed acceptance is derived from
B7; minimum size in both frames gives the full comparison iff. The exact
expanded/final/partial-frame target is now equivalent to shared minimum
transport in both directions. Bounded two-way shared minima supply all smaller
public observations at the same bound. The remaining work is to discharge
those transport premises for arbitrary recipes, including multiplication and
remaining local/successful cases; B8 itself remains open.

[Expanded non-ciphertext multiplication minima](helios-expanded-multiplication-minima.md)
now close that local transport case. Source-minimum children yield normal
fusion partitions; smaller shared minima reassemble into a globally minimum
source representative with the same value in both frames. The argument uses
only forward smaller-minimum transport. Generic competitor comparison and
shared reassembly are reused by initial and expanded frames. Ciphertext-valued
multiplication, remaining local/successful cases and the global two-way
shared-minimum induction remain open.

[Expanded constructed ciphertext minima](helios-expanded-constructed-minima.md)
now close public constructor minimum closure and local constructor transport
without smaller-test premises. Opaque public nonce provenance and original
selected-key/group bounds exclude cheaper competitors. Constructed-only
products compress strictly; existing syntax key transfer supplies destination
values even for nonminimum assemblies, and two-way smaller minima finish
shared transport. Mixed ciphertext multiplication, remaining
local/successful transport and global two-way induction remain open.

[Expanded honest ciphertext minima](helios-expanded-honest-minima.md)
now prove global minimum size for every nonempty honest selector combination,
including competitors using all published handles. Exact indexed occurrence
bags determine costs. Honest combinations themselves are shared minima without
smaller-test premises. A nonminimum ciphertext product of minimum children has
exact child assemblies and a constructed-or-mixed group. With constructed-only
transport checked, mixed products remain the ciphertext multiplication frontier;
remaining local/successful transport and the global two-way induction are open.

[Expanded mixed ciphertext compression](helios-expanded-mixed-compression.md)
now closes mixed assemblies with at least two public constructors under the
two smaller-minimum hypotheses. Exact occurrence bounds make compression
strict, and actual ciphertext values derive election-key agreement in both
worlds. Minimum mixed competitors have one constructor, the same honest index
bag, an equal public nonce and an equal zero-padded payload. One-node payloads
with minimum nonces give global mixed minima. The remaining mixed case has
one constructor and needs global padded payload minima with published numeric
handle costs; remaining local/successful transport and global induction stay open.

[Expanded padded payload minima](helios-expanded-padded-minima.md)
now account for cheap published numerals, preserve exact atom occurrences and
supply global minima under zero-padded equality. Accepted numeric tables make
the same replacement valid in both assignments. The one-constructor mixed case
is closed, and all multiplication classes are assembled in
`accepted_expanded_minimum_children_mul_shared_of_two_way_minima` under the two
strict smaller-minimum hypotheses. Remaining local pair/selector and
successful-case transport and the global simultaneous induction remain open.

[Expanded pair and selector minima](helios-expanded-pair-selector-minima.md)
now close pairing and both selectors without smaller-test hypotheses. Minimum
honest-field matches reuse retained old recipes and B7; nonempty tails have
exact indexed syntax and size, while empty tails use bottom. The complete
local assembly now reduces expanded, partial and final static equivalence to
`Frame.DecryptCheckTransport` in both directions. Only successful decryption
and successful proof checking remain; generic simultaneous induction and all
presentation lifting are connected conditionally to those two transports.

[Expanded successful proof checks](helios-expanded-successful-checks.md)
now close `checkspk` under two-way smaller minima. Constructed proofs reuse the
generic four-test argument; honest bindings use exact minimum combination
origins and retain the complete ciphertext. The remaining B8 interface is
`Frame.SuccessfulDecryptionTransport` in both directions. All other operators,
simultaneous induction and presentation lifting are connected. B8 local
coverage is 11/12; successful decryption, unconditional final-frame equivalence
and B9/B10 remain open. Top-level milestone coverage stays 7/10.

[Expanded public decryption](helios-expanded-public-decryption.md) now
closes direct E5 and E6 with publicly constructed partials, including actual
published partials used as structured keys. The remaining case is borrowed E6:
`ExpandedTrusteeBindingTransport` must transfer a minimum ciphertext's complete
tally binding in both directions, at the original strict induction bound.
Binding already transfers for every retained old public recipe through B7.
All three frame equivalence targets are connected conditionally to this exact
residual proposition. Nested new-handle binding remains unproved; B8 local
coverage stays 11/12 and top-level milestone coverage stays 7/10.

[Result-handle realization](helios-result-handle-binding.md) now gives every
public old-plus-results recipe one shared public initial realization. Full
unbounded equality and complete tally binding follow from B7, including all
nested numeric-result uses. The remaining trustee-binding callback is needed
only for minimum ciphertexts without a result-only presentation. A real
accepted result-nonce fixture refutes old-only minimum syntax: a ten-node
minimum tally match expands to fourteen nodes under numeral realization.
No minimum-size preservation is assumed. B8 remains 11/12 locally and 7/10
in top-level milestone coverage; general trustee-dependent binding is open.

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

[Termination and normal-form existence](helios-rewriting.md) and
[confluence modulo E0](helios-confluence.md#global-confluence) are checked.
Full E equality is equivalent to joinability, and irreducible E-equal terms are
E0-equal. [Full-E passive-constructor injectivity and separation](helios-full-structure.md)
are also checked, along with public-key injectivity and exhaustive projection
paths. [Restricted-name and composed-nonce non-deducibility](helios-nonce-nondeducibility.md)
are checked for frames satisfying the explicit protection invariant. The
[initial historical frames](helios-historical-frames.md) instantiate those results
for any positive candidate count and both swaps. Honest proof validity and
corrected acceptance are checked, including acceptance after the other fresh
honest voter. [Minimum public-recipe existence and replacement facts](helios-minimal-recipes.md)
are checked, including ordinary irreducibility and semantic E5–E7 cancellation.
The [historical minimum-recipe origin induction](helios-minimal-recipes.md#minimum-historical-origins-and-destructor-composition)
is now checked. It derives ciphertext-product certificates and exact
constructed/honest-selector/product syntax, plus constructed or honest-selector
proof origins. Every minimum decrypt retains normal-form composition without
an assumed ciphertext certificate. Minimum projections either select from a
bounded honest tuple tail or compose their normal argument/result values modulo
E0. Public-name, historical-frame and representative-normality premises remain
explicit; no universal substituted-normality claim is made.
The [full candidate-substitution reconstruction](helios-candidate-substitutions.md)
completes source Lemma 9 with the authorised tail-guard correction. It derives
nonce-public explicit ciphertext tuples for all valid ground honest candidate
substitutions, including abstention and reducible representatives, and preserves
literal candidate bits before substitution. Both borrowed proof branches are
excluded. `Historical.General.frame` is the full candidate model; the old
selected-index frame is a specialization. The remaining obligations include
static equivalence of
honest ballot frames and final partial-decryption frames, and a labelled
transition relation with a bisimulation proof.
The [static-equivalence interfaces](helios-static-equivalence.md) now preserve
the caller's full name policy in reconstruction, reduce candidate representations,
and transfer acceptance and a shared constructor witness under an explicit
static-equivalence hypothesis. That hypothesis remains unproved.
The [enriched-ciphertext analysis](helios-enriched-ciphertexts.md) identifies a
counterexample to the paper's open-variable E0 reflection step and replaces the
local numeric argument with exact offset invariance. Honest product equality
now recovers the complete nonce-index multiset, including repeated factors.
The [mixed-ciphertext reduction](helios-mixed-ciphertexts.md) extends this to
a public encryption multiplied by honest factors, reducing equality to the
occurrence bag and strictly smaller nonce/padded-payload observations. Their
swap invariance remains an explicit premise.
The [grouping theorem](helios-ciphertext-grouping.md) now covers arbitrary
constructed/honest product trees recovered from minimum ciphertext recipes,
including semantic key agreement and original-recipe observation bounds.
The [ciphertext observation induction](helios-ciphertext-observations.md) now
transfers key coherence and all grouped comparisons from strictly smaller public
equality tests, giving the actual minimum-ciphertext branch. Its smaller-test
premise remains unproved for arbitrary recipes.
The [proof-valued induction branch](helios-proof-observations.md) uses the same
premise, with honest nonce provenance, all four constructed-proof arguments and
the exact single-candidate component/aggregate coincidence.
The [public-key-valued branch](helios-public-key-observations.md) derives exact
constructor/election-handle origins and transfers their equality tests under the
full secret-name policy and the same smaller-observation premise.
The [initial-frame partial-decryption branch](helios-partial-decryption-observations.md)
derives explicit constructor syntax for every minimum recipe of that value
head and transfers both ordered argument tests under the same bounded premise.
The [pair-valued branch](helios-pair-observations.md) now handles constructed
pairs and nonempty ballot tails. Fresh nonce provenance and suffix length
identify equal tails; comparisons involving constructed pairs use smaller
public tests against both projections.
The [atomic branch](helios-atomic-observations.md) forces minimum recipes for
names and constants to be literal atoms. Their values survive any destination
frame exactly, so this branch needs no smaller-test or freshness premise.
The [destructor observation results](helios-destructor-observations.md) classify
successful minimum projections as honest fields/nonempty tails and derive exact
origins for stuck-check-valued minima. Smaller whole-check/ok probes preserve
check failure, after which the three argument tests transfer equality.
The [stuck projection/decryption results](helios-stuck-destructors.md) derive
exact minimum recipe heads and full-E argument injectivity. They transfer
source equalities forward through smaller argument tests without assuming
destination stuckness. The [partial-key decryption probes](helios-decryption-probes.md)
now derive destination failure and both equality directions when minimum
decryption arguments have partial-decryption and ciphertext source values.
The [minimum value-shape results](helios-value-shapes.md) now discharge those
argument-shape premises by simultaneous reflection. Every minimum decryption
and stuck projection retains failure, and both complete minimum equality
branches transfer in both directions. The
[composition branch](helios-composition-observations.md) now transfers equality
through full-E factor bags and smaller public leaf tests, retaining duplicates
and deriving both worlds' factor conditions. The
[addition branch](helios-addition-observations.md) now derives both worlds'
semantic atom conditions and retains numeric presence/count through exact
summary accounting. Smaller leaf tests transfer equality, including minimum
zero/one recipes with addition E-values. The
[non-ciphertext multiplication branch](helios-multiplication-observations.md)
now retains internal ciphertext fusions and derives smaller public group
recipes in both worlds. Their transferred equalities reassemble the original
products. The global smaller-observation premise and arbitrary-recipe closure
remain open.
Arbitrary public recipe observations and final partial decryptions remain open. The existing finite experiments
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
