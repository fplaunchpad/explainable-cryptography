# Computational Helios: external efficiency argument and closing audit

The computational case study is complete under the revised boundary: Lean checks
coverage and the cryptographic reduction, while the two external arguments below
justify attacker membership and exact reduction efficiency. The main milestone
count is **3/3 under that boundary; publication package is complete**. This is the fixed
three-voter, two-candidate, one-honest-trustee game, with its documented schedule,
repair, shared random oracle, rejection behavior and full public result. It is
not a claim about corrupt trustees, arbitrary schedules or larger elections.

The earlier closing audit on 2026-09-15 found that input-sensitive query bounds
did not directly supply `PreparedFamily`'s global caps. That historical finding
remains correct. The subsequently checked encoded-family and clocking theorems
now derive the missing correspondence; the old incomplete-coverage verdict no
longer describes the current package. The [results ledger](helios-results.md)
retains both outcomes and their separate evidence.

## Exact family and theorem boundary

The final theorem is `ElectionSecurityFamily.Family.ballot_secrecy` in
[ElectionSecurityFamily.lean](../../ExplainableCrypto/Helios/Computational/ElectionSecurityFamily.lean).
For an original family `A`, it concludes negligibility of `A.bias`: the absolute
guessing bias of the original `ElectionOracle.preparedGame`, interpreted by the
actual shared-cache handler from empty storage. The following are all the
resource and parameter fields carried by `Family`; they are explicit premises,
not properties inferred from the word “attacker.”

| Family fields | Exact requirement |
| --- | --- |
| Scalar/group type parameters | For every `n`, `q n` is prime; `G n` is an additive commutative group and a module over `ZMod (q n)`, with decidable equality. |
| `representation` | Group encodings are injective, with length bounded by one natural-coefficient polynomial at `n`. |
| `scalarWidth`, `scalar_width` | The binary width `(q n).size` has a polynomial upper bound. Public scalars use their canonical representative's bits. |
| `fingerprint`, `fingerprintWidth`, `fingerprint_width` | Fingerprint output width is polynomial for every typed parameter record with candidates `[0,1]` and eligible identities `[0,1,2]`. This includes every group/scalar assignment to that record. |
| `generator`, `generator_injective` | `r ↦ r • generator n` is injective. This is the algebraic condition used by the finite reduction. |
| `Init`, `Saved`, `encodeInit`, `encodeSaved`, `init_injective`, `saved_injective` | Private-state families have injective bit encodings. Their sizes below are actual encoding lengths. |
| `prepare`, `adversary` | The original preparation and stateful cast/guess callbacks are retained. |
| `prepareCost`, `prepare_queries` | Preparation makes at most `prepareCost.eval n` queries on every typed response path. |
| `initGrowth`, `prepare_size` | Every preparation output has encoded length at most `initGrowth.eval n`. |
| `castCost`, `cast_queries` | Casting is query-bounded by this polynomial evaluated at `n + encoded Init length + encoded PublicPrefix length`, for every typed input. |
| `savedGrowth`, `cast_size` | Every cast output's encoded `Saved` length is bounded by this polynomial at the same actual input size. |
| `guessCost`, `guess_queries` | Guessing is query-bounded by this polynomial at `n + encoded Init length + encoded Saved length + encoded PublicResult length`, for every typed input. |

The five resource functions are `Polynomial Nat`. Callback bounds and output
support quantify over all well-typed replies, including inconsistent repeated
hash answers. They do not assert callback machine efficiency. Membership of
uniform strict PPT implementations is external claim E1 below.

Public lengths in those fields are the literal `encodePrefix` and `encodeResult`
lengths from [ElectionPublicEncoding.lean](../../ExplainableCrypto/Helios/Computational/ElectionPublicEncoding.lean).
Generic injectivity preserves every public field; `prime_prefix_eq` and
`prime_result_eq` identify the existing prime codecs exactly.
`prefix_length_le` and `result_length_le` account for nested framing with fixed
factors `100000000` and `10000000000` times the structural widths. These loose
constants are proved bounds, not measurements or additional caller premises.
[ElectionPublicBounds.lean](../../ExplainableCrypto/Helios/Computational/ElectionPublicBounds.lean)
derives the reached structural bounds from the actual source: at most two board
entries before casting, at most three afterward, and successful decoded values
at most three. Rejection and decoding failure remain present.

`Family.prepared` keeps preparation unchanged and gives casting/guessing derived
polynomial query clocks. Its private saved type is `Option Saved`, with an
explicit zero-ballot/absent-state fallback. The reached-input bounds prove that
fallback is never taken in the original game. `Family.coverage` establishes
complete `OracleComp` equality, and `Family.run_coverage` preserves the full
output and final shared cache from every starting cache. `Family.bias_eq`
identifies the original bias. Thus no game-correspondence or global callback-cap
hypothesis is supplied to the final theorem.

Beyond `A : Family q G`, `Family.ballot_secrecy` has exactly four hypotheses:

| Hypothesis | Meaning |
| --- | --- |
| `hsize` | `noncePointBound (ZMod (q n))` is negligible. This is a lower-growth requirement on field size, separate from encoded-width upper bounds. |
| `hmain` | `MainReductionEfficient A.prepared A.representation`: for every fixed accuracy degree `k`, the exact normalized main reduction has one uniform finite realization and one polynomial time bound. |
| `hreject` | `RejectionReductionEfficient A.prepared A.representation`: the same claim for the exact normalized rejection reduction. |
| `hddh` | `DDHAssumption A.representation A.generator`: DDH against the explicitly defined uniform machine class under the same group representation. |

The lower-level
[ElectionSecrecyConditional.lean](../../ExplainableCrypto/Helios/Computational/ElectionSecrecyConditional.lean)
still preserves the old explicit hash/total-query hypotheses. The new family
theorem discharges them using its derived clocks; the old
[fair-bit secrecy theorem](../../ExplainableCrypto/Helios/Computational/ElectionSecrecyFairBits.lean)
is unchanged. Efficiency is always asserted for **`A.prepared`**, because equality
of the original game law alone would not transfer efficiency through altered
replay paths.

The named efficiency predicates are defined in
[ReductionEfficiency.lean](../../ExplainableCrypto/Helios/Computational/ReductionEfficiency.lean).
These are definitions of linked implementation claims, not proofs of reduction
efficiency. `Realization` contains one finite `NativeOracleTape.Code`, its entry
label, a fixed polynomial time bound, termination with an actual Boolean output
on every coin path, and equality of the full Boolean output distribution with
the supplied family on every encoded challenge. Code and time cannot depend on
`n` through a pointwise choice. The main family may select different code and
polynomials for different fixed `k`.

The input is unary `n` followed by four separately delimited group words.
`GroupRepresentation` requires injective encodings and a polynomial width bound;
`inputWord_length` derives the bound `n + 8*width(n) + 5`. This width policy is
an explicit family assumption. It does not follow from negligible inverse field
size. The representation is also used in the DDH assumption.

There are no hash, storage, arithmetic or callback oracles in a realization.
The syntactic `coinOnly` condition forbids hash commands for every control/head
combination. The remaining oracle response is exactly one fair bit. Primitive
operations, callbacks, cache lookup/update, copying and replay must all execute
inside the finite code and its time bound. No runtime is assigned to a Lean
function merely because it appears in the source program.

### Relation to conventional PPT: external argument

`NativeOracleTape.Code` reads a finite label and three current cells, and chooses
from finitely many commands. A local command performs at most three ordinary
head moves/writes. The witness's `coin_ready` invariant requires the answer tape
to be blank before every coin command. The native replacement therefore writes
one random bit; it cannot erase an arbitrarily large tape in a charged single
step. Clearing work before the next coin must use local instructions.

Consequently this restricted machine is an ordinary finite three-tape
probabilistic machine up to a fixed step convention. Encoding its finite control
and simulating the local commands has constant-factor overhead on a conventional
multitape model; usual tape simulation yields polynomial overhead on a single
tape. Its polynomial-length input and polynomial running time also bound the
visited tape region. This is the external justification for applying conventional
PPT DDH to the class in `DDHAssumption`, under the same representation policy.
It is **not** a Lean adequacy theorem or a consequence of `IsOraclePPTBy`.

The output-law requirement is exact for the fair-bit reductions. The previously
proved sampling-loss transport relates these reductions to the original ideal
range-sampling game. No additional sampling approximation is introduced here.

`Controls.constant_false_efficient` exhibits a complete realization of the
constant-false family. It establishes that the generic predicate is inhabited,
not that either exact reduction is efficient or that all cryptographic family
and DDH hypotheses are jointly realizable. Other controls reject missing halt,
blank output, a wrong output law, hash access and nonblank coin-answer state.

## External efficiency argument for the reductions

This is external claim E2, for the exact normalized family `D = A.prepared`.
It is conditional on the uniform implementations and width policies stated
below. These conditions justify the named efficiency hypotheses mathematically;
they are not consequences of `Family`'s query bounds and are not introduced as
new global Lean axioms. No Lean realization of either full reduction is claimed.

1. The chosen family has effective public parameter/scalar representations and
   uniform polynomial-time implementations of the actual group/field operations,
   comparisons, serialization and fingerprint function. Scalar and group values,
   fingerprint outputs and all query indices have polynomial encoded widths.
2. Preparation, casting and guessing have uniform implementations with strict
   polynomial local runtime on the relevant polynomial-size inputs and every
   admitted response path, including simulated and altered replay challenges.
   The bound covers suspended machine configurations, not only public results
   or the `Init`/`Saved` values. Oracle handling is charged separately below.
3. Every callback-requested range `t+1` has polynomial binary width. This applies
   on the replay and simulation paths as well as ordinary honest execution.
   A single range query can otherwise request an unbounded amount of randomness.
4. Use the **actual** normalized budget: `D.p n = A.prepareCost.eval n` and
   `D.c n = A.castCap.eval n`. These are evaluations of fixed natural-coefficient
   polynomials, so their uniform computation is polynomial time. Main uses their
   sum to choose its repetition count. Replacing the original family's budget
   by an unrelated dominating polynomial would change that exact reduction;
   here the chosen polynomials are its definitions. Evaluate the cast/guess
   clocks and the fixed-degree accuracy/repetition counters explicitly.

For each fixed accuracy degree `k`, let `W(n)` be a common polynomial envelope
for these representations, full callback configurations, oracle responses and
counter widths. Its coefficients may depend on that fixed degree. Strict callback
runtime bounds imply polynomial workspace in the conventional machine model;
enlarge `W` accordingly. Let `Aprep`, `Acast`, `Aguess` bound local callback work,
including deterministic processing between oracle calls. Let `b` be a fixed
polynomial bounding arithmetic, framing, copying and elementary record handling
on words of length at most `W(n)+n`. Enlarge `b` to dominate uniform parameter
setup, fingerprint evaluation and evaluation of the actual `D.p+D.c` function;
their polynomial runtime is also part of the assumptions above.

### Checked query and replay bounds

Write `p=D.p n`, `c=D.c n`, and let `P,C,J` denote the theorem's total callback
query bounds at `n`. Define

\[
M=4P+4C+78,\qquad
R_k=3456(p+c+10)^3(n+1)^{4(k+1)}.
\]

[`ElectionDDHSource.honestReject_total_bound`](../../ExplainableCrypto/Helios/Computational/ElectionDDHRejection.lean)
checks the complete rejection reduction's bound `M`.
[`ballotSecrecy_prime_cost`](../../ExplainableCrypto/Helios/Computational/ElectionDDHReduction.lean)
checks the main bound
`(1+3R_k)M+4+4J`. `ElectionSecrecyPrototype.replay_bounded` derives a polynomial
envelope for `R_k` from the hash budget, for each fixed `k`. These count actual
oracle interactions, including the cast in the rejection prefix. They do not
charge local computation or assert a polynomial jointly in varying `k`.

### Storage and suspended executions

The checked [`runBallotFiniteCache_eq` and `runBallotFiniteCache_length_le`](../../ExplainableCrypto/Helios/Computational/BallotFiniteCache.lean)
connect finite live-ballot storage to the original semantic cache and bound its
entries. [`ballotFork_log_bound`](../../ExplainableCrypto/Helios/Computational/BallotFork.lean)
and [`ballotReplayCollectTape_length_le`](../../ExplainableCrypto/Helios/Computational/BallotReplayTape.lean)
bound logs and recorded answers. The frozen scratch results
`HandlerSubstitution.CacheActualReplay.actual_lower_empty` and
`CacheStorage.open_empty_bounds` additionally cover the actual auxiliary
key/decryption handler from empty storage, with an entry bound and abstract size
`N*(Kmax+Vmax+1)`. Their evidence is in the results ledger's upstream substitution
experiment; these particular scratch results are not imported into the root build.

Externally implement dictionaries and logs as finite lists of encoded entries.
Each relevant query adds at most a constant number of entries across the
auxiliary/live/programmed stores and logs. The source's fixed honest programming
adds only a fixed number. A prefix with at most `M` interactions therefore stores
`O(M)` records. Scanning, inserting, comparing and copying those records costs at
most `O(M²*b(W+n))` over the prefix. Width bounds, including stored callback
states, are essential to this argument.

Existing `BallotCacheBitSize` bounds include actual record framing;
`CacheLookupMachine.run` and the insertion machine results account for concrete
prime-group live-ballot cache operations. These are supporting checked pieces.
They do not automatically certify the auxiliary election-key codec or the full
new realization. Extending the finite-list implementation to those fixed-arity
key constructors and proving the complete implementation relation are external
steps in this argument.

[`ballotJointReplayRepeatAtPath` and `replayRepeat`](../../ExplainableCrypto/Helios/Computational/BallotReplayRepeat.lean)
close over one immutable original path and repeat that same attempt. A failed
residual's enlarged state is not fed into the next attempt. `ballotReplayAtPath_first` retains the original
path; `prefix_repeated_original` retains the complete original output/live law.
The final [`extractedGame` and `finishExtracted`](../../ExplainableCrypto/Helios/Computational/ElectionDDHExtractedFinish.lean)
resume the original state/cache and use the original `Init` and `Saved` for
guessing.

A finite implementation can retain callback snapshots, or reconstruct a snapshot
by rerunning the original callback with its recorded answers. Charge all snapshot
copying, transcript scans and reconstruction. Their size and work are polynomial
under the configuration-width/runtime assumptions. This is an implementation
argument, not a claim that arbitrary `FreeM` continuations are finite code.

### Exactness of the external implementation

Maintain a representation invariant: each auxiliary/live/programmed dictionary
looks up the same answers as its source cache; the sticky flag and ordered
history represent the source state; callback snapshots contain the actual
suspended configurations; replay tapes contain the same ordered queries and
answers. On a cache hit return the stored answer without sampling. On a miss
perform the source's bounded fair-bit sampling and then its insertion. Source
programming uses its actual occupied-key rule and retains the distinct live
cache; it is not replaced by unconditional reinsertion.

The query cases of
[`ElectionReplaySource.lower_run`](../../ExplainableCrypto/Helios/Computational/ElectionReplaySource.lean)
identify the source interpretation being implemented. The finite-list lookup
and update cases preserve the dictionary invariant. The assumed correct uniform
primitive/callback implementations preserve the value/configuration invariant.
A replay copies or reconstructs the recorded snapshot and follows the source's
selected altered answer and subsequent sampling; it does not reuse a failed
attempt's successor as a new original. Induction over this finite executed
sequence preserves the invariant, including the actual timeout branches of the
normalized callbacks and the final original-state continuation.

Using the same fresh fair bits for each corresponding source draw gives the
same emitted values and final Boolean on each coupled execution. Hence the
resulting finite implementation has the exact output distribution required by
`Realization.correct`. The runtime argument below bounds that implementation;
this is an external representation/implementation proof, not a claimed Lean
compiler from arbitrary `OracleComp` syntax. In particular, no extraction
success, accepted-ballot or good-event condition is used to omit a branch.

### Fair bits and total work

[`sampleFairBitRange_query_bound`](../../ExplainableCrypto/Helios/Computational/FairBitSampler.lean)
checks that a range `t+1` at slack `n` uses at most `(t+1).size+n` fair-bit queries. The source reads that fixed number of bits
and reduces modulo the requested range; it has no unbounded rejection loop.
An ordinary binary implementation constructs the sampled integer and performs
division/modulo in polynomial time in its bit length. Reserve the native answer tape for the single coin cell: copy each sampled bit
into working storage and clear that cell before the next draw. This maintains
`coin_ready` with constant overhead per bit. Uniform scalar sampling must use
the corresponding represented prime-field implementation. The exact
distribution and statistical slack are already covered by the sampler and
`ElectionDDHFairBits` theorems; the binary runtime implementation is external here.
[`primeScalarSampler_total_bound`](../../ExplainableCrypto/Helios/Computational/PrimeSamplers.lean)
exposes the actual scalar sampler as
`(ZMod.finEquiv q) <$> uniformSample (Fin q)`, fixing the index conversion that
the implementation must preserve.

For a conservative bound let `S=M+J+1`. Linear dictionary implementations and
explicit snapshot costs give envelopes of the form

\[
T_{reject}=O(Aprep+Acast+M²b(W+n)),
\]
\[
T_{main,k}=O((1+3R_k)(Aprep+Acast+S²b(W+n))
                 +Aguess+S²b(W+n)).
\]

The final `S²` term includes oracle handling during guessing against the retained
cache; guessing queries are not free. The formulas deliberately overestimate
storage and copying. Every factor has a polynomial envelope for fixed `k` under
the stated conditions. There is no iteration of one failed attempt's storage
growth into its successor. These are handwritten asymptotic bounds, not checked
instruction counts or supplied Lean cost certificates.

## E1: external membership of intended strict PPT attackers

Fix the documented protocol/parameter policy and a uniform, explicitly
polynomial-clocked strict oracle-PPT implementation of preparation, casting and
guessing. Use faithful canonical encodings for its persistent `Init` and `Saved`
configurations and the public encodings used by `Family`. The clock convention
charges writing query indices, reading/processing replies, copying configurations
and serializing returned private states. It applies on every admitted random
tape and every well-typed reply sequence, not only replies consistent with one
hash function.

A callback's strict time polynomial in unary `n` plus its actual encoded input
length bounds both the number of queries and the length of its serialized private
output. Enlarge its coefficients and constant to obtain `Polynomial Nat` bounds.
Preparation gives `prepare_queries` and `prepare_size`; casting gives
`cast_queries` and `cast_size`; guessing gives `guess_queries`. Persistent machine
state, rather than only a chosen public fragment of it, must be included in the
private encoding. This supplies the resource fields of `Family` without assuming
any game correspondence.

Hash replies have the stated canonical scalar width. A uniform-range query names
`t+1` through an index that the attacker must write; its binary width is bounded
by the callback's time, and a reply has at most that width. The parameter policy
supplies polynomial scalar/group widths, effective primitive operations and
fingerprint computation on the fixed parameter shape. The checked public
serialization bounds, output-growth bounds and polynomial compositions then
provide parameter-only clocks on reached inputs. Lean proves that those clocks
preserve the original tree and cached game law. Query counts alone do not prove
any of these local-runtime or implementation claims.

This convention must not be silently replaced by “runtime bounded only against
consistent random-oracle functions.” A program can query one key twice and take
additional steps only when the answers differ. The finite controls
`fixed_hash_two_requests`, `inconsistent_hash_three_requests` and
`consistent_bound_not_syntactic_bound` in
[ElectionCoverageControls.lean](../../ExplainableCrypto/Helios/Computational/ElectionCoverageControls.lean)
show exactly two requests under every fixed singleton-key handler but three in
the complete source tree. They refute transfer of the same finite bound, not an
asymptotic PPT claim.

For a program known to run within a uniform strict polynomial on all consistent
executions, an external clock-normal-form argument is available: run that code
with its known time bound as a counter and use an explicit timeout result. The
counter never expires on genuine cached executions, so queries, private state
and outputs there are unchanged; other reply sequences are stopped. This is an
external normalization argument, not a theorem supplied by `Family.coverage` for
an arbitrary pre-existing unclocked source callback. The stated membership claim
uses the explicitly clocked model. An expected-time-only guarantee requires a
separate treatment and is not included.

## Trust and assumption boundary

| Layer | What is relied on | Evidence and limit |
| --- | --- | --- |
| Lean kernel and libraries | The checked proof terms and the pinned Lean/mathlib/VCVio definitions; standard axioms `propext`, `Classical.choice`, `Quot.sound` where printed. | Query-clock transparency, public encoding/size, exact source/cache coverage and the cryptographic theorem are kernel checked. No new global efficiency axiom is declared. |
| Cryptographic model | The selected fixed election, typed group/scalar and public encodings, original oracle semantics, full rejection/tally observations, and the explicit finite coin-only machine convention. | These define the theorem's meaning. They do not assert wire-parser security or a different corruption/scheduling model. The finite machine convention's ordinary-PPT interpretation is the external argument above, not a Lean characterization theorem. |
| Mathematical cryptographic assumptions | Prime/module family, generator injectivity and representation/width policies in `Family`; negligible `noncePointBound`; DDH for the same representation and machine class. | They remain hypotheses. The constant-false realization does not establish their joint satisfiability or a concrete asymptotic group family. |
| External claim E1: attacker membership | Uniform explicitly clocked strict PPT implementations yield the encoded query/growth fields for every typed reply path. | The argument above charges input/output handling and private configurations. Consistency-only runtime assumptions require the separately stated external normal-form argument. |
| External claim E2: exact reduction efficiency | The normalized main family for every fixed `k`, and the normalized reject family, have uniform coin-only realizations with the exact output law and polynomial worst-case time. | The implementation and quantitative argument above uses checked source/query/cache/replay facts. It remains external; query bounds and component machines do not by themselves construct these complete Lean witnesses. |

`MainReductionEfficient` and `RejectionReductionEfficient` are concrete linked
execution/correspondence claims, not arbitrary predicates or abbreviations for
negligible DDH advantage. No generic compiler, backend closure theorem or
standard-PPT machine characterization is part of this completion claim.

## Non-efficiency audit and evidence

| Obligation | Final status |
| --- | --- |
| Parameter family, representations and widths | Explicit `Family` policies; no concrete asymptotic family is constructed. |
| Original input-dependent query and private growth bounds | Explicit local `Family` fields; E1 explains strict PPT membership. |
| Global preparation/cast/guess and hash caps | Derived for `A.prepared`, with polynomial domination and computable replay-budget definitions. |
| Source and persistent-cache correspondence | `coverage`, `run_coverage` and `bias_eq` prove it for the original family. No correspondence premise remains. |
| Rejection, extraction, field-size and fair-bit losses | Existing finite/asymptotic reductions derive them; `accuracy_admissible` derives the eventual extraction side condition from `hsize` and polynomial hash bounds. |
| Fixed protocol policy | Three voters, two candidates, one honest trustee, fixed eligible schedule and the documented repair remain the accepted case study. |
| Exact normalized reduction efficiency | E2 and the two named theorem hypotheses; no completed general machine compiler is claimed. |
| Historical positive-attack transport | Existing attack/repair results are retained. Further shared-oracle transport is a separate validation extension, not a premise of the repaired scoped secrecy theorem. |

The original
[EfficiencyInputControls.lean](../../ExplainableCrypto/Helios/Computational/EfficiencyInputControls.lean)
counterexample is retained: one query per list element admits no fixed bound
across all input lists. It does not refute clock normalization. The coverage
controls check a polynomial input-dependent class, every input up to a selected
width, exact two-versus-three query counters and exclusion of an extra query.
The width-two fixture is not an election-size assertion.
[ElectionFamilyControls.lean](../../ExplainableCrypto/Helios/Computational/ElectionFamilyControls.lean)
provides passive and querying family instances under explicit cryptographic
policies. Its length-sensitive example keeps the reached cast unchanged while
changing an over-wide, unreachable private input. Public encoding controls keep
the fingerprint visible and distinguish decoding failure from zero. These are
finite source controls, not tests of DDH hardness.

Targeted checks, the integrated computational build and exact-name axiom audit
for the coverage package pass. The [results ledger](helios-results.md) records
commands and evidence under `tmp/helios-coverage-2026-09-15/logs/`, including
`coverage-integrated-build.log`, `axioms.log`, `audit-summary.json` and
`preservation.json`. The publication build, document audit and PDF review are
recorded by the enclosing publication increment; this document does not infer
their completion from a targeted module check.

The final package closes the specified coverage obligation and the three main
milestones under the revised two-external-argument boundary. The publication package is complete. Earlier internal-machine construction checkpoints and possible model
extensions are not retroactively marked proved, and milestone counts are not
estimates of effort.
