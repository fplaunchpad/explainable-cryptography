# Static equivalence: transfer interfaces and controls

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

Source Lemma 10 is machine-checked in the encoded model by
`Historical.General.initial_frame_staticEq`, for fresh names and all valid
ground candidate substitutions under `Names.restricted`. It compares every
pair of public recipes modulo the full theory E, with no remaining observation
or shared-minimum premise. See the [initial-frame proof](helios-initial-static-equivalence.md).
B8 is complete. [Published transcript static equivalence](helios-published-static-equivalence.md)
proves all public equality observations for the actual partial and final frames,
including arbitrary nesting of trustee-partial and result handles. Freshness,
valid ground candidates, public initial-handle submissions and their sequential
acceptance are explicit; no local-transport or static-equivalence callback remains.
All twelve expanded operator cases are closed. The next milestone is B9:
process transitions, adaptive-recipe flattening and matching. B10 labelled
bisimilarity and the full symbolic secrecy theorem remain open. Coverage is
8/10 unweighted milestones (80%), not an effort estimate.

The development history below records earlier conditional interfaces. Initial
and published-frame theorems now discharge their former B7/B8 hypotheses.

The later [enriched-ciphertext analysis](helios-enriched-ciphertexts.md) refutes
the encoded E0 reflection to open vote variables used in the paper's Claim 2.
It proves corrected numeric-offset invariance and full-E equality characterization
for nonempty honest ciphertext products. The subsequent
[mixed-ciphertext reduction](helios-mixed-ciphertexts.md) handles arbitrary
public nonce and payload subrecipes in an encryption multiplied by a nonempty
honest product. Its swap-transfer theorem retains the two strictly smaller
observation premises. The [grouping bridge](helios-ciphertext-grouping.md)
recovers arbitrary constructed/honest assemblies from minimum ciphertext recipes
and groups their contributions with semantic key and original-size evidence.
The subsequent [ciphertext induction step](helios-ciphertext-observations.md)
transfers key coherence and the complete grouped equality matrix from smaller
public equality tests. It applies to actual minimum ciphertext recipes without
assuming second-world coherence or preservation of minimum syntax. Establishing
its smaller-observation premise globally and the all-recipe static-equivalence
obligation remains open. The [proof-valued branch](helios-proof-observations.md)
is also checked under the same hypothesis, including the one-candidate equality
between component and aggregate proof fields. The
[public-key-valued branch](helios-public-key-observations.md) also derives its
minimum origins and transfers the key-form comparisons under the full policy
and smaller-test premise. The
[initial-frame partial-decryption branch](helios-partial-decryption-observations.md)
now derives explicit constructor origins and transfers both ordered component
tests under the same premise. Frames publishing partial decryptions still need
additional cases. The [pair-valued branch](helios-pair-observations.md) now
derives constructed/nonempty-tail forms, identifies equal tails from length
and fresh aggregate nonces, and transfers comparisons involving constructed
pairs through smaller projection tests. The [atomic branch](helios-atomic-observations.md)
now derives literal syntax and exact evaluation preservation for minimum recipes
with name/constant values, without a smaller-test premise. This still does not
transport arbitrary nonminimum evaluations. The
[destructor observation results](helios-destructor-observations.md) now derive
origins for all stuck-check-valued minima and transfer equality using smaller
ok probes and argument comparisons. Successful minimum projections are
classified as honest field/nonempty-tail syntax. The
[stuck projection/decryption results](helios-stuck-destructors.md) now derive
exact minimum origins and full-E argument injectivity. Their source equalities
transfer forward using smaller tests without destination stuckness premises.
The [partial-key decryption probes](helios-decryption-probes.md) derive
destination failure and both equality directions for minimum decryptions with
partial-decryption-valued first arguments and ciphertext-valued second
arguments. The [value-shape results](helios-value-shapes.md) now discharge all
argument-shape premises and derive failure for every minimum decryption and
stuck projection. Both complete stuck-destructor minimum equality branches
transfer in both directions. The
[composition branch](helios-composition-observations.md) derives indivisible
semantic factors and transfers their full-E bag equality from smaller leaf
tests. The [addition branch](helios-addition-observations.md) now derives
semantic atom conditions and exact numeric accounting in both worlds, including
literal zero/one minima. Its equality transfers from smaller public leaf tests.
The [non-ciphertext multiplication branch](helios-multiplication-observations.md)
now derives normal partitions with smaller public group recipes and exact
original bounds, retaining internal ciphertext fusions. Transferred group
equalities reassemble the original products. Arbitrary nonminimum evaluation
transport and the global smaller-observation premise remain open. The validation
counts below belong to the earlier transfer-interface increment.

The transfer interfaces below are machine-checked. They preserve the full source
scope while making the remaining static-equivalence premise explicit. Use the
[task list](../../task%20list.md) for development status; source Lemma 9 is already
complete with the authorised [tail guard](helios-symbolic-tuple-guard.md).


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

## Preserve the caller's public-name policy

Source Lemma 9's reconstruction is public under the honest nonce restriction.
Applying static equivalence to its equality requires the stronger restriction
that also forbids the secret key and auxiliary name. An existential witness
public under the former policy cannot silently be treated as public under the
latter. Nor does minimum size under one policy imply minimum size under another.

[PublicReconstruction.lean](../../ExplainableCrypto/Helios/Symbolic/PublicReconstruction.lean)
proves reconstruction under any caller-supplied `restricted` set containing
`ns.nonceNames`. The input recipe must be public under that set. The proof
chooses minimum component-proof recipes under that same policy and extracts
public nonce subrecipes. The nonce-only aggregate exclusion still applies,
using `Term.Public.of_subset` to weaken the input publicness along the explicit
inclusion of nonce names. All reconstructed nonce and proof recipes, and the
complete ciphertext tuple, retain the caller's policy.

The remaining premises are the same as in source Lemma 9: acceptance with the
corrected tail guard and both actual honest ballots on the board. The theorem
covers every positive count, both swaps, honest abstention and arbitrary valid
ground representatives. Literal bit witnesses satisfy `CandidateValues` in the
recipe type before substitution. The original nonce-only theorem remains valid.

## Representation reduction and shared witnesses

[GeneralStaticTransfer.lean](../../ExplainableCrypto/Helios/Symbolic/GeneralStaticTransfer.lean)
separates two obligations:

- `staticEq_iff_representatives` proves that componentwise E-equal replacements
  of the two candidates preserve the vote-swap static-equivalence proposition
  in both directions.
- `staticEq_of_bit_candidates` reduces the general candidate proposition to
  static equivalence for every pair of valid literal `BitCandidate` vectors.
  That remaining hypothesis still includes honest abstention and every public
  recipe; it is not a finite-catalogue or exactly-one assumption.

These results do not establish static equivalence between different votes.
They show how a proof on literal representatives will cover the original
arbitrary ground substitutions.

`accepted_ballot_common_constructor` assumes static equivalence of the two
actual general frames. It applies the stronger reconstruction in the left world,
then transfers its equality using the fully public original and reconstructed
recipes. One existential witness therefore works for both `swap` values. The
public conclusion retains all nonce/proof publicness conditions, the literal
candidate bits before substitution, and both E-equalities.

`accepted_ballot_common_components` exposes the corresponding component values:
the same literal plaintext vector explains the adversarial ciphertexts in both
worlds. The nonce recipes are shared; their evaluated values may differ. This
supplies a premise needed for the source Lemma 11 tally argument. The newer `accepted_sequence_common_data` and
`accepted_sequence_tally_numeric` discharge that initial-frame hypothesis and
prove the numeric tally result for actual sequential acceptance. Final-frame
static equivalence remains open.

## Acceptance is publicly observable

[StaticAcceptance.lean](../../ExplainableCrypto/Helios/Symbolic/StaticAcceptance.lean)
works for arbitrary frames with the same restriction and handle domain. It
proves that aggregation commutes with substitution and preserves publicness,
then expresses every acceptance condition as a public equality test.

| Claim | Evidence | Declaration | Required premises |
| --- | --- | --- | --- |
| Input publicness survives removing restrictions | machine-checked | `Term.Public.of_subset` | Explicit inclusion; no minimum-size claim |
| Component nonce reconstruction preserves the caller's policy | machine-checked | `Historical.General.accepted_component_public_nonce_of_policy` | Policy contains honest nonces; public input, acceptance and both honest board members |
| Complete tuple reconstruction preserves that policy | machine-checked | `Historical.General.accepted_ballot_constructor_recipe_of_policy` | Same premises; explicit public output and source candidate sum |
| Vote representations preserve the swap obligation | machine-checked | `Historical.General.staticEq_iff_representatives` | Componentwise E-equalities of both candidates |
| Literal candidate static equivalence suffices | machine-checked | `Historical.General.staticEq_of_bit_candidates` | Static equivalence for all valid bit-vector pairs remains assumed |
| One public reconstruction works in both worlds | machine-checked | `Historical.General.accepted_ballot_common_constructor` | Actual frame static equivalence, full-policy public input and accepted left-world ballot |
| Shared literal component plaintexts | machine-checked | `Historical.General.accepted_ballot_common_components` | Same conditional scope |
| Component and aggregate proof checks transfer | machine-checked | `Frame.StaticEq.proofValid_iff` | Static equivalence and public key/ballot recipes |
| Corrected tail guard transfers | machine-checked | `Frame.StaticEq.tailGuard_iff` | Static equivalence and public ballot recipe |
| Component weeding transfers | machine-checked | `Frame.StaticEq.noReuse_iff` | Same list of public board recipes evaluated in each frame |
| Full corrected acceptance transfers | machine-checked | `Frame.StaticEq.accepted_iff` | All the preceding public-recipe premises |

All declarations are in `ExplainableCrypto.Helios.Symbolic`. No arbitrary ground
board is silently assumed to be publicly reproducible. The board in
`accepted_iff` is explicitly a list of recipes, evaluated separately in each
world. This is the interface needed for later process matching; no process
transition relation is supplied by these lemmas.

## Independent controls

`StaticEquivalenceSPOT.lean` retains two concrete distinguishers:

- Reusing one nonce at two candidate positions makes the first honest ballot's
  ciphertext fields E-equal for abstention and E-unequal for a selected vote.
  Both recipes are public even under the full policy. This proves failure of
  static equivalence without the source's fresh-name condition.
- The nonce-only policy permits naming the secret key. A public decryption
  recipe under that policy returns zero in one world and one in the other.
  The full restriction forbids that recipe. This is a checked counterexample
  to using the nonce-only policy for Lemma 10.

With fresh nonce names, the first equality probe is false in both worlds. An
honest component check succeeds in both worlds, excluding universal stuckness
as an explanation. The represented and literal versions of the same vote also
instantiate an all-recipe positive static-equivalence theorem.

The gate's observation proxy has a checked limitation:
`raw_aggregate_observer_incomplete` proves a general-frame aggregate check
E-equal to `ok` while its raw-normalized value differs syntactically from `ok`.
The missing E0 numeric simplification is substantive; the raw normalizer must
not be used as a full-E equality decider.

`PublicReconstructionSPOT.lean` uses the public-key handle to construct a fresh
abstaining adversarial ballot after both honest ballots. It instantiates the
conditional shared-witness theorem on identical honest votes, where static
equivalence is proved, and independently recovers nonce 40 and plaintext zero
in both worlds. The returned complete tuple is public under the full restriction.
The acceptance-transfer control uses a nonempty public board and separately
proves that actual replay is rejected in both worlds. These controls do not
claim privacy for different votes.

## Gate and validation

`StaticObservationExperiments.lean` compares the equality matrices of 28 recipes
over the two fresh-name general frames. The catalogue includes public fields,
homomorphic products, component and aggregate checks, fresh known-key
ciphertexts, ordinary and partial decryptions, selectors and tuple tails.
It uses literal abstention/selection candidates at counts one through five and
varies selected positions. The 256-input backstop includes all 20 count/pair-mode
configurations, with both worlds evaluated on each input; the full Cartesian
product of selected positions is not claimed.

The gate compares raw-normalized syntax, so its result is restricted executable
observation evidence. All three campaigns pass at seeds 1, 7 and 42, with 500
configured cases per seed, maximum size 40 and `gaveUp=0`. All 256 backstop inputs
pass. The nonce-collision and exposed-key negative controls each fail at generated index n=0,
seed 1, zero shrinks. Their Lean counterexamples establish the corresponding
full-E distinctions independently of the proxy.

Reproduce with:

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/StaticObservationExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
python3 scripts/check_helios_claims.py
```

The full build passes (3447 jobs), including 24 new public theorem type/axiom
audits. The audit has 1069 nonempty axiom reports using only `propext`,
`Classical.choice` and `Quot.sound`, plus 17 axiom-free reports. No warnings,
errors or `sorryAx` occur in the completed build. The local evidence log is
`tmp/variable-overlap/static-transfer-full-build.log`.

The independent source is Cortier–Smyth Appendix B.3, Lemmas 10–11. Trusted
definitions remain the encoded equational theory, public recipe semantics,
frame restriction, candidate sum, proof checks, weeding and corrected guard.
No cryptographic equation or public operation changed. No static-equivalence
assumption was added as an axiom. Proving the all-recipe literal-candidate swap
case, then tally and final partial-decryption results, remains the next work.
