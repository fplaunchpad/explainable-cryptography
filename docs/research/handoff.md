# Continue on another machine

Current position: **3/3 computational milestones complete under the revised
boundary; publication package complete**. The publication package is complete; the subsequent target split preserves the
case study in the default build and the deferred development in `HeliosExecution`. The historical
symbolic B1–B10 theorem remains complete and unchanged. These are coverage
milestones, not estimates of effort.

`ElectionSecurityFamily.Family.coverage` and `.run_coverage` derive exact
original-game/shared-cache agreement for encoded, input-bounded attackers.
`.ballot_secrecy` derives negligible original bias from negligible reciprocal
field size, DDH and efficiency of the exact normalized main/rejection fair-bit
reductions. `ElectionPublicBounds` and `ElectionPublicEncoding` derive reached
record bounds and faithful serialized lengths. Uniform PPT coverage and complete
reduction efficiency use the explicit external argument; Lean retains their
named efficiency hypotheses. No whole-reduction native compiler is claimed.

Use [task list.md](../../task%20list.md) for the sole development status,
[the dependency map](helios-proof-blueprint.md#computational-proof-dependencies)
for the proof chain, and [the closing audit](helios-computational-closing-audit.md)
for the revised external/mechanized boundary. The
[scope comparison](helios-scope-comparison.md) records the intentional symbolic
and computational protocol differences; no cross-model correspondence is proved.

Run `lake build` and `python3 scripts/audit-helios-computational.py` for the case
study. To reproduce deferred execution evidence, first run
`lake build HeliosExecution`, then audit with
`python3 scripts/audit-helios-computational.py --scope full`.
The [source guide](../../ExplainableCrypto/Helios/Computational/README.md#build-targets)
records the retained roots and import-set check. No further proof goal is active.

The PDFs now have separate audiences and builds: the
[mathematical reference](../formal-reference/main.pdf) presents the games,
theorems and assumptions; the [historical catalogue](../formal-reference/catalogue.pdf)
preserves component evidence with obsolete status assertions removed.
Use `bash scripts/build-formal-reference.sh --document reference` or
`--document catalogue`; the first uses only the default build. Both publications
have source/axiom checks and rendered-page review. No new proof goal is active.

## Earlier machine experiments and checkpoint handoffs

The following entries preserve their historical evidence and reproduction
commands. Their former 2/3 and C1–C12 frontiers describe those increments, not the
current revised completion claim. They do not authorize TM cleanup or resume a
retired implementation route.

The general native oracle round-trip experiment is integrated/audited within
its authorized 09:23:15–10:53:15 UTC window on 2026-09-15. Targeted importer, framed
export/import, actual native/source event and complete charge proofs pass.
The controller freezes the native-selected kind/continuation before conversion,
uses the original bounded hash interface (both coins remain), replaces the whole
answer and returns to that selected live native entry.
`NativeRoundTrip.execution_correspondence` and `.native_correspondence` check the
complete event tree and represented native successor. `.framed_correspondence`
and `.framed_cost` include arbitrary private words with the same derived charge.
Root integration, complete audits and reviewed reference §14.134 pass.

The resident input has arbitrary finite optional-Boolean cells, including
internal and trailing blanks; output/query scratch starts empty. The answer's
old right half is replaced by the actual oracle event, its old left half is
cleared by executed instructions, and the reply becomes the ordinary native
word tape. Work/query contents and their original heads are retained. The importer
and whole-code independent gates pass; exact evidence belongs in the results
ledger. This one-call result does not execute the continuation or establish
arbitrary-program compilation, external startup packing, standard-PPT coverage
or full reduction efficiency. C5 remains partial; counts stay 2/3 and 6/12.

The preceding 90-minute general query-export experiment has a proved result.
`NativeQueryExportFrame.charged` and its result/storage theorems cover arbitrary
finite head/before/after cell lists, including internal blanks and retained
postblank data, with arbitrary independent private words. Executed head
preparation/restoration, full original storage and scratch restoration are
derived. Source clock `2*after.length+6` and charge at most `12*after.length+36`
come from the actual instructions. Root build, full audits, both gates and reviewed reference
§14.133/Theorem 14.163 pass; this increment is integrated/audited. Run `lake env lean scripts/NativeQueryExportGate.lean` for the
core and actual-head exhaustive/mutation gates. The completed round-trip experiment
above supplies one-call reply import and dispatch; external startup and full
compiler coverage remain open. The sole backlog is task list.md.

The separately authorized 90-minute native compilation experiment now has a
proved fixed-program result with the root build, complete audits, independent
controls and reviewed reference §14.132 passing; the increment is integrated/audited. `NativeAdaptiveRun.exact_run`/`.native_correspondence` connect an
actual finite native hash/branch/coin/dependent-hash program to generated code,
retaining all private words and the complete final answer, with both replies
arbitrary. `NativeAdaptiveCost.within` and
`.physical_run` derive source/physical cost under the existing bounded adapter.
Run `lake env lean scripts/NativeAdaptiveCompilerGate.lean` for the independent
full-state/event/cost and source-mutation gate. This starts in resident dense
stacks; startup packing and general native/PPT coverage remain open. The bounded experiment is complete; stop further construction at this result. The sole
backlog and exact bounded acceptance are under C5 in task list.md.

Completed bounded [execution architecture assessment](helios-proof-blueprint.md#bounded-execution-architecture-assessment).
The general two-call test is checked and C5/C6/C7/C8/C9/C12 are assessed.
The increment is integrated/audited. Stop further protocol construction here.
The ultimate computational theorem and original checkpoint criteria are unchanged.

`PrimeProofRequest.charged`, `.execution_source` and `.run_support` check a
complete resident request. `PrimeProofRequestReentry.charged` now checks actual
cleanup and nonce preparation; its wrong writer-port counterexample is retained.
`PrimeRemainingProofRequests` derives both p1/total presentations and retained
frames, including zero modular sum. `PrimeRemainingProofCaller` links the same
executor twice after the original raw prefix. Its full-state native gate and two
fault controls pass. `PrimeRemainingProofCallerRun` now proves the full combined
raw source tree, halt, derived charge and physical execution.
`PrimeRemainingProofSource` connects the original two queries to the final
proof/state encodings. Final integration audits and reference review pass.

The local reuse route is demonstrated; full native attacker coverage and exact
reduction runtime remain architectural uncertainties. Do not continue another
source-specialized arithmetic chain or infer all-PPT efficiency from query counts.

Earlier checked frontier: p1's original flat hash key is serialized on port 70, with
all 70 prior words retained. `PrimeSecondKeyMachine.charged_source` derives the
actual operands, blank workspace, coordinate bounds and key codec from the
completed commitment state, reusing the existing writer unchanged.
`PrimeSecondKeyCaller.execution_source`/`.physical_run` pass targeted checks
from the original raw input with the unchanged fair-bit source tree and derived
combined physical cost. The native gate passes 7 canonical cases/9 mutations/1
rejection, seeds 118/606/20260914, no discards/gaveUp; independent full-state
controls pass. Complete integration audits and reference review pass.
Reproduce the gate with `python3 scripts/check_second_key.py`.

That earlier key-specific chain stops at its source presentation. The shared
resident executor now performs both remaining proof updates and returns, using
the current shadow cache, sticky flag and duplicate-preserving history. `PrimeSecondProgramSource.source_fields`, `.source_context` and `.source_lengths`
derive these resident inputs and their current `N+1` bounds; `.successor_counts`
bounds the semantic next state by `N+2`. Fresh/occupied branch and proof-return
facts describe the original source, without executing the update. Preserve the separate live cache and old proof/nonces; do not
restart from the stale saved state inside raw14. The overall proof and later
election/PPT execution remain open. C6 stays partial; no checkpoint closes.

Previous integrated/audited frontier: all four p1 commitment coordinates and preparation.
`PrimeSecondCommitTail.charged_source` executes B, canonical d, adjusted beta,
C and D from the actual first-coordinate result, with full retained state and
derived charge `96*K + S + 32*G`. The five local source interfaces derive all
operands and frames; their actual instruction gates and independent controls
pass. `PrimeSecondAllCommitCaller.execution_source` and `.physical_run` now
pass targeted checks: original raw input reaches the full70-word result with
unchanged draw tree and derived prefix-plus-tail charge. Physical startup and
execution use the actual combined code's compiler factor and arbitrary bounded
adapter limit, without an assumed input origin or cost certificate. The root
build, complete audits, checker tests and reviewed reference §14.128/
Theorem14.155 (pages172–173) pass. Evidence is recorded in the results ledger.

The preceding first-coordinate increment is integrated/audited in §14.127/
Theorem14.154 (pages170–172), including raw source and physical cost. The next
C6 obligation after key serialization is programming the current saved state
and returned-proof encoding, then the overall proof and later election. No checkpoint
closes: C6 stays partial and all-PPT secrecy remains open.

The preceding integrated boundary passes all source/runtime targets and audits.
`PrimeRemainingProgramSource` checks exact p1/pt source factorization;
`PrimeSecondTranscriptSource` derives the actual second-call inputs, retained
frame, work and widths. `PrimeSecondTranscriptMachine.charged` and MachineSource
execute the second ciphertext and four fresh draws with derived branch charge.
`PrimeSecondTranscriptCaller.execution_source`/`.physical_run` connect the original
raw input with full state and total physical cost. Typed endpoint controls pass.
The instruction gate covers eight distinct fixtures, nine mutations and one
rejection across retained directed/mutation results and an isolated seeded
retry. Both timeout attempts remain recorded; controller/driver hashes and
modeled caps are unchanged. Root build, complete audits, checker tests and reviewed §14.126/Theorems
14.151–14.153 (pages 168–170) pass; this increment is integrated/audited. The commitment continuation above advances
that successor; programming/return, the overall proof and later election remain. This prefix does not close C6 or secrecy.

Previous programming boundary: `PrimeProgramCaller` executes the original raw
first-proof prefix through cache insertion, sticky collision handling, cleanup
and ordered history prepend. The full reached state matches the actual
`BallotFiniteProgrammedState.program` successor for arbitrary finite initial
shadow/live states, including agreeing occupied values. The separate live cache,
nonces, key, challenge and original raw context are retained. Root build,
complete audits, independent controls and reviewed reference
§14.124/Theorems 14.145–14.147 pass. This increment is integrated/audited;
C6 remains partial.

Previous output boundary: `PrimeProgramProofSource` identifies the original returned
proof and canonical resident operands; `PrimeProgramRepackSource` derives the
updated saved-state shape and enlarged bounds from the original input length.
Its checked `saved_changed` theorem excludes reusing the old saved record.
The preserving `BitPairWriterMachine` has complete local execution/charge proofs
and independent controls. The fixed `PrimeProgramOutputMachine` passes its
original-code gate: six canonical boundary cases, ten mutations and one guard
rejection. Its complete Run, typed source and raw-caller composition now pass targeted
checks. The actual original raw input reaches two separately encoded words:
returned proof on 48 and updated saved state on 49, retaining all preceding
48 words and the unchanged draw tree. Total charge and physical execution
bounds are derived. Root build, complete standard-axiom, symbolic and reference
audits, independent controls and checker tests pass. Reviewed reference
§14.125/Theorems 14.148–14.150 (pages 166–168) is synchronized; this output
increment is integrated/audited. C6 remains partial.

The next source continuation retains the nonce pair and first proof, requests
`p1` at `(false, rs.2)` and `pt` at `(vote, rs.1 + rs.2)`, and permits the modular
sum to be zero. Port 14 retains the original raw input with its old saved state.
Reentering the whole prefix would resample and repeat the first proof. Actual
continuation routing, later ballot construction/verification, C5 attacker
coverage and complete adaptive cost remain open. Use only the task list as the
backlog. The checkpoint records below describe earlier boundaries; their local
limitations do not undo subsequently checked components.

Previous integrated key-serialization increment: PrimeSimKeyMachine executes the complete
original eight-field key from the actual commitment state, preserving all old
words and deriving charge. Typed source, independent literal controls and code
mutation gates pass. PrimeSimKeyCaller now connects original raw input to the
exact key and complete retained state with derived total physical cost. Root
build, complete standard-axiom and symbolic/reference audits, checker tests and
reviewed §14.122/Theorems 14.139–14.141 pass; this increment is integrated/audited.
At that boundary, canonical programmed-state operands and executed updates
were still pending. The subsequent extraction and programming increments now
derive them; opaque saved bytes alone remain insufficient evidence.

Preceding integrated C6 frontier: `PrimeSimAllCommitCaller` checks original raw input
through both nonce draws, first ciphertext, all four simulator draws, canonical
challenge difference, adjusted beta and every actual first-ballot simulator
commitment coordinate. Full source tree, final state, aggregate charge and
physical execution are derived. `source_commitments` explicitly identifies
outputs3/38/40/42. Source/frame/cost premises are derived from preceding actual
results. Local component gates and complete43-word final controls pass.

The raw difference campaign passed one p3/q2 record and its skip mutation with
600s host response allowance; the unchanged300s attempt timed out without a
returned mismatch and remains recorded. Modeled clocks and charge caps did not
change. Its nonce space is a singleton. Final finite tail/raw composition uses
checked label/full-state return identities and component code gates; no further
full raw-native campaign is claimed. Root build, complete standard-axiom and symbolic/reference audits, five checker
tests and reviewed reference §§14.119–14.121 pass. This increment is
integrated/audited.

At that earlier commitment boundary, statement/key encoding and programmed-cache
updates were pending. They now have the integrated results above; remaining
ballot construction and complete adaptive execution/cost are still open. C5 effective attacker coverage is still
required. The first simulated commitment construction does not close C6, C7 or
the all-PPT secrecy goal. See only the task list for remaining tasks.

Earlier integrated C6 source: `CacheRequestMachine.request_run` executes one complete request
from a canonical serialized key/cache/log/sampler record, through actual parsing
and a success gate. Its full query tree, final ports, halt and charge are derived;
`.physical_run` includes blank-work physical input loading. Loaded-width bounds
retain public p/q widths, the private record and log count-header growth.
Root build, exact-name standard-axiom audit, symbolic/reference gates, eleven
kernel controls and native loader/wrapper mutations pass. Reviewed §14.106/
Theorems 14.110–14.112 (pages 134–136) is synchronized and integrated/audited.
The original-request bound increment now passes root build and exact-name
standard-axiom audit. `CacheRequestPrefixes` derives erasure, supported lifting,
capture retention and prestate budgets; `CacheRequestPrefixBounds` derives
encoded widths, actual hash-request charge and historical `n+15` specialization.
Explicit request/family polynomials and independent arithmetic/observer mutation
controls check. PDF §14.107/Theorems 14.113–14.114 (pages 136–138) is compiled and
visually reviewed; this request-bound increment is integrated/audited. The
resident entry/return connection is recorded below. Actual source operand
production, response decoding/continuations and combined adaptive cost remain
open. See only `task list.md` for remaining obligations.
The outer host caller is still a specification, with no assumed general compiler.

The resident caller entry/return now also passes root build and full standard-
axiom audit: `CacheCallerMachine.load_request` ends at the live dispatcher label;
`.request_run` preserves the complete request tree/result and private saved word
with derived charge. Source observation, prefix clock and primitive execution
are connected in `CacheCallerMachineSource`. The 525-case native gate detects
four mutations; nine kernel controls include reentry on a returned miss result.
Reference §14.108/Theorems 14.115–14.116 (pages 138–140) is compiled and
visually reviewed; this component is integrated/audited.
C6's actual source operand production, uniform/saved-context policy, decoding/
continuations and combined adaptive cost remain open. The concrete
`primeNonceValue` successor now checks in `PrimeNonceMachine.successor_run`,
with full scratch/frame equality and derived charge. Root build, six kernel
controls and 1,024 native fixtures pass; full standard-axiom audit and reviewed reference §14.109/Theorem 14.117 (pages 140–141) pass; this successor component is integrated/audited.
The complete nonce sampler now checks in `PrimeNonceMachine.sample_source`,
with executed predecessor/width preparation, exact full source tree and combined
charge. `.sample_loss` retains the one-draw error; `.sample_physical_run` derives
the physical bound from resident input/frame. Native/kernel controls pass;
root build, full standard-axiom audit and reviewed reference §14.110/Theorems 14.118–14.119 (pages 141–143) pass; this complete single-nonce component is integrated/audited. The following increment closes nonce-pair invocation/storage; the honest
constructor remains next, with C7 arithmetic and C5 attacker-interface dependencies.

The actual nonce-pair caller now checks in `PrimeNoncePairMachine.pair_run` and
`.pair_execution_source`: executed copies, clean reentry, two successive draws,
both saved results and the exact historical joint source tree. `.pair_loss`
retains the two-draw bound; `.pair_physical_run` derives complete cost from the
resident record/context. Native and kernel controls pass; root build, full standard-axiom audit and reviewed reference
§14.111/Theorems 14.120–14.121 (pages 143–145) pass. This pair increment is
integrated/audited. Loaded modular multiplication now checks in
`BinaryModMultiply.run`, `.group_coordinates` and `.physical_run`: actual
preparation, full result/cleanup, coordinate source equality and derived charge
and primitive execution bound. Root build, full standard-axiom audit and reviewed reference
§14.112/Theorems 14.122–14.123 (pages 145–147) pass; this multiplier
increment is integrated/audited. Loaded power now checks in
`BinaryModPower.run`, `.group_coordinates` and `.physical_run`, with retained
original exponent/context and derived width/physical bounds. Native/kernel controls, root build and full standard-axiom audit pass; reviewed
reference §14.113/Theorems 14.124–14.125 (pages 147–149) is integrated/audited. The two-power ciphertext controller now checks in `PrimeEncryptMachine.run`,
`.source` and `.physical_run`: actual operation calls, original `encryptWith`
coordinates, complete retained state and derived physical bound. Its 210-case
native gate and nine full-state kernel controls detect seven code mutations.
Root build, full standard-axiom audit and reviewed reference
§14.114/Theorems 14.126–14.127 (pages 149–150) pass; this loaded
ciphertext component is integrated/audited. Actual public/nonce-pair input routing
and proof-request encoding remain open. C5's effective attacker interface
and complete adaptive execution/cost remain open; C6 remains partial.

The execution layer now has an actual primitive oracle loop, reusing Mathlib's
pinned compilers and the existing physical oracle I/O. Target control is proved
finite throughout execution; reconstruction retains every non-tape field.
`BitOraclePrimitiveBounded.run_source_bounded` / `.run_source_handler` preserve
complete caller results, native queries and lawful handler effects at clock
650*G*B*(H+B+V+1)^2. The original source halt/charge and bounded-answer contract
remain explicit; compiler correspondence and intermediate halt are derived.
The adaptive canary derives its own source bound.

This increment is integrated/audited: root build, exact-name standard-axiom
audit, eight new controls and reviewed reference §14.89/Theorem 14.91 (page 115)
pass. Earlier execution layers and independent fixtures are recorded in the
[results ledger](helios-results.md).

Physical initial loading now checks in `BitOracleInitialInput.load`: blank
working storage reaches the complete canonical ready state within 4|input|+8
steps. Its source-clock/handler theorem composes this startup with the primitive
loop. Input bits, including malformed encodings, are loaded unchanged; parsing
and operand distribution remain source work. Root build, exact-name axiom audit,
six controls and reviewed reference §14.90/Theorem 14.92 (page 116) pass; this
increment is integrated/audited.

`BitTapeCoverage` now supplies the local-computation component of that coverage:
ordinary blank/false/true tape transitions run in the existing source language,
with derived charge at most seven per native step and a connection to the
primitive compiler. Native oracle I/O remains open;
this is not full attacker coverage. Root build, exact-name axiom audit, six
controls and reviewed §14.91/Theorem 14.93 (page 117) pass; this local component
is integrated/audited.

Raw input conversion and its link to native execution now check in
`BitTapeStart.physical_run`. Starting from blank work storage, it derives the
complete native result and a polynomial clock from input length and the native
halt bound. Seven controls include actual physical/primitive execution; source
conversion and correspondence are derived. Root build, exact-name axiom audit
and reviewed §14.92/Theorem 14.94 (page 118) pass; this connection is
integrated/audited.

`NativeOracleTape` fixes the remaining three-tape reference interface. Its
native events agree with the existing dispatcher and preserve full work/query
tapes for every reply. Six controls include a private-frame counterexample to
work/answer aliasing. This is interface agreement; its source compiler and full
attacker coverage remain open. Root build, exact-name standard-axiom audit and the reviewed reference
§14.93/Theorem 14.95 (pages 118–119) pass; this interface agreement is integrated/audited.

The conditional completion prototype now checks in
`ElectionSecrecyPrototype.prepared_negligible_of_ddh`. It derives negligible
bias for the original prepared-election family from polynomial hash-query
budgets, negligible reciprocal field size, and DDH security of the two exact
reductions. For every fixed degree k it uses e(n)=(n+1)^(k+1); the eventual
field-size condition and a polynomial bound on actual replay counts are derived.
This does not establish local runtime, sampler/standard-PPT correspondence or
DDH security of those reductions. A checked counterexample shows that fixed
linear extraction accuracy is not negligible. Four controls and 3,000 independent
arithmetic fixtures, root build, exact-name standard-axiom audit and reviewed
reference §14.94/Theorem 14.96 (pages 119–120; theorem page 120) pass. The
conditional prototype is integrated/audited.

Sampling transport now checks in
`ElectionSecrecyFairBits.prepared_negligible_of_fair_bits`: the original
prepared-election bias is negligible under security of the exact fair-bit main
and rejection DDH reductions. Their complete query bounds and negligible
sampling losses in both DDH worlds are derived from polynomial callback
budgets. The challenger distributions remain exact. Five controls and 750
independent finite DDH enumerations, root build, exact-name standard-axiom audit
and reviewed reference §14.95/Theorem 14.97 (pages 120–121; theorem page 121)
pass; this increment is integrated/audited. This closes
probability-law sampling composition, not effective modulo/group operations or
standard-PPT efficiency. Next: complete C6's scalar execution and cost, needed
to justify the fair-bit reductions' remaining runtime premises.

`BinaryModuloMachine.run` now executes complete binary division on a loaded
little-endian word and positive canonical modulus. It returns canonical remainder
digits, retains the modulus and clears input and scratch, within
N*(8*q.size+13)+2 TM2 ticks. The proof derives the remainder/width invariant and
counts input reversal, linked subtraction and both return-transfer passes.
Seven Lean controls, 16,352 exhaustive cases and 1,500 seeded cases pass;
root build, standard-axiom audit and reviewed reference §14.96/Theorem 14.98
(pages 121–122) pass. This closes C6's second acceptance condition;
connecting coin loading to division and scalar digit handoff remain.
`CoinWordLoader.run_source` now executes chronological coin loading with exact
source cost; `.word_index`/`.run_modulo` relate its numeric observation to the
original sampler. Five controls, root build, standard-axiom audit and reviewed
reference §14.97/Theorem 14.99 (page 123) pass. Width/modulus loading, linking
actual division stacks and scalar digit handoff remain open at that boundary.
`CoinModuloMachine.run_source` now links the actual coin loader to division in
one fixed program, preserving the complete oracle tree and full output frame,
with derived clock and charge. `.sampler_value` matches the original modulo
sampler. Five controls, 2,032 exhaustive/750 seeded cases, root build, exact-name
standard-axiom audit and reviewed reference §14.98/Theorem 14.100 (page 124) pass.
Width/modulus loading and scalar writer/cache-handler handoff remain.

The immediate route is endpoint-first: discharge the exact DDH premises through
C5–C8 execution, sampling and efficiency, and C9 family/control integration.
Further low-level machine construction is deferred until its role in that
assembly is explicit. C12 now has a conditional asymptotic result; the all-PPT
secrecy milestone remains open. Counts remain 2/3 main and 6/12 supporting.

`ElectionDDHSource.prepared_ballot_secrecy_ddh_bound` bounds the original shared-
oracle prepared game's winning bias by two actual DDH advantages plus
18/(q−1)+3L+2/e, L=(11p+2c+131)/q. Its stated premises are generator/scalar
injectivity, all-proof-hash preparation/casting bounds p/c, e>0 and
12(p+c+10)e≤q, with the existing field/module/sampling instances. The guessing
callback remains arbitrary. `ballotSecrecyDistinguisher` runs the actual
public-input extracted game; the secret-using hybrid is confined to the proof.
`ballotSecrecy_real_gap`, `.ballotSecrecy_random_gap` and `.completed_random_win`
derive the real/random comparisons and exact ideal one-half endpoint.
`honestRejectDistinguisher` separately accounts for rejection in both DDH worlds.
`ballotSecrecy_prime_cost` derives the matching complete uniform-index query
bound, including original execution, replay, trustee publication and guessing.

All 1572 public computational theorems pass exact-name axiom audit with
standard axioms only. Root build and six reduction controls pass, including a
q=65537 querying/view-dependent fixture with explicit non-DDH allowance below
1/2. The reviewed reference §14.74/Theorem 14.76 (pages 98–100, theorem on page 99) is synchronized. The task list and results
ledger retain the C10/C11 acceptance audit and source dependencies. Detailed
prior intermediate results remain in the ledger/reference; they are no longer
open correspondence premises.

C9 repair-control increment: `ElectionOracle.repairedAttackWorld_rejected`
now checks probability-one reuse rejection from every shared initial cache;
fixed-hash correspondence identifies the complete original execution and sampled
world. The exact neutral-proof query is executed. Six Lean controls and 240
independent multiplicative executions pass. Root build and exact-name standard-axiom audit pass. Reviewed reference
§14.75/Theorem 14.77 is on pages 100–101 (theorem page 100). The C9 checkpoint
remains open; the results ledger records reproduction.

C5 raw-port increment: `BitOracleCanary.run_source` now checks a fixed
finite-control TM2/hash/coin interface on H(x), H(H(x)), H(x), retaining the
halted configuration and exact proposed length charge. Five Lean controls and
1524 independent raw-word fixtures pass. Root build, exact-name standard-axiom
audit and reviewed reference §14.76/Theorem 14.78 (pages 101–102) pass. This is
not the scalar-backed election-handler canary or a standard-machine cost theorem.
The actual local transfers are now checked below; their standard oracle-tape
translation remains open; the assembled interpreter is now checked below.

C5 port transfers now execute in TM2: `BitOraclePortTransfer.hash_transfer`
and `.coin_transfer` derive the exact caller successor, preserve saved finite
memory and restore empty private ports. The bound is nine times the interface
charge in TM2 ticks/native events. `hash_handoff` / `coin_handoff` connect the
actual raw queries and complete response-phase starts. Six dedicated controls,
99,351 independent cases, root build and exact-name standard-axiom audit pass.
Reviewed §14.77/Theorem 14.79 is on pages 102–103 (theorem page 103). Standard
oracle-tape translation and scalar-handler integration remain open. The
assembled loop and finite source correspondence are now checked above. Reuse these phases; the results ledger records the append/stale-
port counterexamples and reproduction.

Remaining work: C9's explicit family/challenge/corruption policy and oracle-aware
historical positive-attack transport; C5's effective standard-PPT attacker/execution
contract; C6–C8's actual arithmetic, saved-context execution and derived machine
costs; C12's security-parameter family and negligible-advantage theorem under
explicit cryptographic assumptions. Do not add another execution layer before
closing the C5 interface decision. The completed symbolic theorem and controls
are unchanged. General election-language and symbolic-to-computational framework
work stays deferred. See `task list.md` for the only development backlog.

## Archived handoff: symbolic proof complete; concrete proof then active

B1–B10 are integrated and audited. The [retrospective reuse report](helios-reuse-retrospective.md)
records frozen dependencies, native CSLib checks, an adapter for the actual
source actions and a checked AFP-inspired frame port. The experiments retain
all original proof assumptions and observations; they demonstrate no positive
net removal. Broader design savings remain unmeasured. No further symbolic
proof or requested reuse-audit obligation remains.

At this archived checkpoint: **2/3 complete; Step 3 (ballot secrecy) active**.
The attack and repair/correctness stages are integrated and audited. Library
selection and toolchain migration are complete supporting prerequisites.
The milestone count does not estimate effort remaining.

Section 4 of `task list.md` recorded that computational goal. All usable Lean
code now shares the root Lean/Mathlib 4.33.1 build, with pinned VCVio and the
computational namespace `ExplainableCrypto.Helios.Computational`. The concrete
public proof-reuse attacker has a checked success bound `1 - 6/(|F|-1)` in the
three-voter, two-candidate, one-honest-trustee cast-only game, with actual
rejection, board updates and trustee publications. See the
[concrete model](helios-computational-model.md) and latest results-ledger entry
for the exact scope and local checks. The BPW-style concrete repair now has
probability-one copying rejection and honest validation/tally correctness, with
accidental honest-pair rejection bounded by `9/(|F|-1)`. The actual ballot Σ-protocol now has checked completeness, special soundness
and honest-verifier simulation within `3/|F|`. Simulator commitment-collision
and conditional-challenge properties now check, retaining their generator and
valid-witness premises. The explicit ballot prover/verifier and simulator use a
shared lazy hash cache, with checked algorithm agreement and answer preservation.
The one-proof state-inclusive distance now checks at `3/|F| + |Q|/|F|`, with
valid witness, injective generator and finite initial cache-cover premises.
Reachable cache budgets and adaptive honest-proof simulation now check, with
state-inclusive bound `p * (3+k+n) / |F|` for the documented structural query
budgets. Raw ballot-oracle replay extraction now checks: the wrapper agrees
with the original runtime, contextual replays preserve the entire target, and
supported extractor outputs satisfy the actual bit/nonce relation. Completing
the existing verifier query gives actual verification acceptance and derived
query coverage in its lower bound, including unqueried targets. Actual accepted
board entries now exclude covered targets, and an accepted generated-honest
statement match implies prefix rejection and nonce collision. The match-event
probability is bounded by 9/(|F|-1); a checked counterexample retains target
recurrence after honest rejection. Local proof simulation preserves accepted
targets. The replayable programmed-cache adapter now checks exact runtime
agreement, reachable live/shadow consistency, request provenance, verification
agreement outside requested statements, and source-to-live query bounds.
Actual honest-ballot requests now preserve the historical nonzero-sampling
and full-constructor distribution, including final cache and flag. Request targets
are derived from returned components/aggregate and compose with prior metadata.
The sampled ballot has derived query bounds and simulation distance.
Actual full-proof oracle submission now preserves proof-before-reuse rejection
and retained boards. The sampled honest pair agrees with the historical pair
sampler plus explicit-coin oracle execution, including board, decisions, cache
and flag. When both actual honest decisions accept, recorded targets belong to
the returned board; actual accepted submission after arbitrary raw attacker
queries excludes them. The rejected case now has an actual real-prefix bound
9/(q−1) and programmed-prefix bound 9/(q−1)+90/q. The latter follows from the
derived six-proof/twelve-request budget and existing state-inclusive simulation;
no flagged execution is discarded. Accepted programmed prefixes have checked
positive probability at q=101; dropping generator injectivity is refuted by a
zero-generator execution that rejects with probability one. The selected-proof
extractor now composes the actual prefix, a raw attacker receiving its decisions
and board, and original submission. Accepted joint executions derive live full
validity; rejected cases cannot contribute a valid fallback. For attacker hash
budget n, the replay budget is n+15 and the verifier completion adds one.
The bound retains the prefix loss; each returned bit/nonce witness belongs to
the selected ciphertext of some supported accepting submission. This source
origin was existential in `_extract_origin`. The new `repairedSubmission_extractSource`
returns the first complete submission, proves it accepted and ties the witness to
its selected ciphertext. Projection exactly recovers the old extractor, so the
bound has no added loss. This uses VCVio's existing `contextForkWitness` paths and
PolyFun's `Path.pullMap`; no new trace format or fork framework was needed.
`repairedSubmission_joint_extract` now samples one original source path and
replays each selected query conditionally at that path. Its successful output
contains all three witnesses for the retained original accepting submission.
Pure trace projections preserve every query answer, and the marginal attempt
exactly recovers the existing raw selected-proof extractor. A joint probability
and efficiency argument remains open; separate successful runs do not suffice.
The algebraic consumer is now checked in `BallotWitnessConsistency`: actual
covered ciphertext witnesses imply nonce/scalar sums, and prime ZMod q with q>2
implies the integer at-most-one count. A four-element characteristic-two control
refutes replacing the characteristic condition by field cardinality >2. This is
an abstract-parameter boundary, not an attack on the historical prime-order scope.
`repairedSubmission_joint_extract_consistent` applies the algebraic consumer to
the algorithm's derived witnesses. The positive control repeats one honest target;
it is not a three-distinct-proof success bound. A checked disjoint-success-set
control refutes inferring joint success from marginal positivity. Accepted-path
coverage now checks: `repairedSubmissionPath_verified`, `_selector` and
`_locations` derive live full validity and all three physical locations from the
actual path cache, acceptance theorem and budget. `_selection_probability`
identifies simultaneous original selection probability with joint acceptance.
The common-path quantitative bound now checks in
`repairedSubmission_joint_extract_le`: with Q=n+16, accepted-submission probability
B, loss ℓ=9/(q−1)+90/q and a=(B−ℓ)₊, success is at least
(a−3Qδ)₊(δ−1/q)₊³. The stronger version uses actual joint acceptance.
`ballotJointReplay_bad_context_le` bounds low-mass original contexts; the product
bound is derived from the actual conditional binds. δ is an analysis threshold,
not an algorithm input. `ballotJointReplay_total_query_bound` now proves at most
4m total oracle interactions from a raw-source bound m, including uniform draws,
one original run and all three attempts. Logging and physical completion bounds
are derived. Actual source accounting now checks in
`repairedSubmissionSource_total_query_bound`: at most 4(m+19), with an explicit
one-query scalar-sampler bound. `repairedSubmission_joint_extract_total_query_bound`
gives 16(m+19), and `_canonical_total_bound` discharges sampler cost for
`SampleableType.ofFintype`. m bounds all attacker interactions per view; the
selector hash-budget n is separate. The finite Mathlib `AList` live-cache interpreter
now has exact `runBallotFiniteCache_eq` correspondence for every raw program;
`repairedSubmissionFiniteCache_eq` instantiates the actual original submission,
and `_length_le` derives at most n+15 entries. The programmed shadow now uses
that same finite carrier. `runBallotFiniteProgrammed_runtime` preserves both
caches, sticky flag and exact request history; `repairedSubmissionFiniteSource_eq`
is exact raw-source equality, so existing replay results apply without a new
state premise. The finite saved-tape implementation now reconstructs the exact
original typed path and all selected physical occurrences. `ballotJointReplayTape_eq`
and `repairedSubmissionTape_extract_eq` retain the original joint algorithm,
including failures, with no new validity premise. Saved tape length is bounded
by 4(m+19) under one-query scalar sampling; canonical sampling retains the
16(m+19) interaction bound. The finite logging interpreter now preserves complete
source executions and the ordered miss log. `ballotFiniteJointReplay_eq` integrates
it into the first run and all three residual attempts; `repairedSubmissionFinite_extract_eq`
retains the actual repaired extractor exactly. Original miss-log length is bounded
by n+15. `repairedSubmissionFinite_storage_le` now derives equal cache/log
lengths and n+15 entries each. `_record_cells_le` bounds the complete key records
by 16(n+15) group elements and n+15 scalar answers. The eight-field key decoder
has exact round trips; a preloaded cache refutes unqualified equal lengths.
`repairedSubmissionFinite_shadow_runtime_storage_le` now derives at most m+19
shadow cache and request-history entries in the actual probabilistic execution,
from attacker total bound m. Arbitrary initial offsets are accounted for by
`runBallotFiniteProgrammed_storage_le`; repeated programming retains duplicate
history. `repairedSubmissionFinite_output_board_lengths` now bounds the actual
output boards by two and three entries. `_output_cells_le` bounds retained ballot
projections by 96 group and 72 scalar cells. `BallotTapeOperandControls.wide_tape`
and `.no_count_only_tag_bound` check that supported one-event tapes can have
arbitrarily wide binary uniform tags. `uniformNatRead_encode` and `_exact` now
prove a canonical binary natural prefix codec; `uniformEventDecode_encode` and
`_exact` cover the actual uniform range/answer pair, rejecting malformed or
out-of-range input and trailing bits. Encoded length depends on both operand
widths. `scalarDecode_encode` and `_exact` now cover historical scalars, rejecting
values at or above q. `replayTapeDecode_encode` and `_exact` cover complete mixed
entropy tapes, including tags, frame lengths, event count and full consumption.
`repairedSubmissionBits_extract_eq` proves that direct encoded-frame collection
and replay from saved bits preserve the exact existing repaired joint extractor.
The existing VCVio ZMod sampler supplies a computable scalar enumeration.
An explicit nonzero nonce sampler now preserves every continuation distribution
and the independent nonce-pair distribution. The explicit-nonce submission
and lowered finite source now preserve the full runtime distribution, including
both caches, request history and rejection decisions. The explicit-source
saved-bit extractor now has derived selector locations, all three valid witnesses,
the historical joint success bound and a 16(m+19) total interaction bound.
No old/new replay correspondence is assumed.
The checked fair-bit obstruction is retained. The actual extra-bit modulo sampler
now has an exact residue law and error at most 2^(-s), using range binary width
plus slack s fair-bit queries. The adapter composes over arbitrary adaptive
uniform requests, preserving supported outputs. Applied through the existing
exact scalar-entropy interpreter, it gives a fair-bit joint extractor with valid
witnesses and the previous success bound minus at most 16(m+19)*2^(-s).
The historical ideal sampler and public rejection behavior are unchanged.
These are sampling and fair-bit-query results; encoded local execution and
machine costs remain open.
The concrete prime subgroup now reuses Mathlib roots of unity over ZMod p.
Its public coordinate operations match the existing ElGamal algorithms; a
nonidentity generator derives injective exponentiation and, for prime p and q,
cardinality q. Canonical group records round-trip, identify every accepted word
and have a modulus-width bound. Identity remains valid; nonmembers and
out-of-range aliases reject in this internal codec. Full election raw-input
parsing and rejection behavior are still a separate obligation.
Complete eight-field hash keys and ordered finite caches now have canonical
bit records. Decoding preserves every key/value and entry order, rejecting
duplicate keys. Encoded lookup distinguishes malformed input from a cache miss;
encoded insertion agrees with the actual finite-cache operation. The explicit
nonce replay source now derives the encoded cache-size bound from its own
n+15 entry budget. These results include framing bits but do not establish
parsing, lookup or insertion runtime costs.
The finite interpreter data now has complete canonical state records: the
chronological miss log, programmed shadow cache, sticky flag, repeated request
history in its stored order, and separate live cache. Encoded programming agrees
with the actual sampled-transcript transition on typed inputs. The explicit
source derives full logged-state and both-cache bit bounds from its own hash
and total-query budgets. These state bit lengths do not establish continuation
execution or execution time.
Proofs, ballots, identified boards, submission results and all fields of the
existing public election views now have canonical bit records. Distinct
rejection decisions, fingerprint, trustee proofs, shares and decoding failures
are retained. An encoded submission wrapper preserves the original shared-oracle
computation; the complete finishing wrapper preserves the existing typed-hash
election output. The actual submission runtime has an internal bit-result
wrapper with exact decoding and a combined output/state bound. Private
interpreter data stays internal. This does not establish raw-input policy,
metadata-width bounds or execution costs for the full election game.
Loaded complete-key comparison now runs in Mathlib's concrete TM2 machine:
two binary stacks and finite control inspect individual heads. The checked run
halts with exact equality within first-word length plus one transitions;
canonical full-key encoding derives a K(p)+1 bound. This counts execution on
already-loaded words. The complete parser and lookup execution appear below. Initial loading,
cache updates and whole-extractor PPT remain open.
Two-pass concrete copying now preserves loaded query/cache words and any
destination suffix, clears scratch and reaches the exact final configuration
within 2*word.length+2 TM2 transitions. Actual supported source caches derive a
2*B(p,q,n+15)+2 bound from their hash-query budget. This copier is reused in
the complete lookup below; initial encoding/loading remains open.
The concrete natural-prefix parser now halts on every raw bit word with a
linear transition bound and exactly matches the existing decoder, including
malformed-input rejection and suffix preservation. Actual supported cache records
supply their own count prefix and a 3*(n+15).size+3 parsing bound. The machine
outputs literal binary digits, used by the complete parser and lookup below.
Canonical binary decrement now executes directly on the parser's bit stacks,
with fuel ≤2*n.size+1, exact predecessor digits, zero-underflow reporting and
unchanged surrounding stacks. Its input invariant follows from the actual
prefix-parser run. A linked field reader now executes the prefix parser,
binary decrement and payload restoration in one TM2 program. Every raw word w
halts with exact field-decoder agreement within 3*|w|+5+(|w|+1)*(2*|w|+4)
transitions. Short inputs are rejected without expanding their declared lengths;
accepted singleton records from the existing codec supply the field framing.
An exact stack-relocation proof now preserves outer count/archive on two extra
binary stacks. One shared-control iteration parses a field, decrements the outer
count, preserves the field/suffix/archive and clears workspace; rejected fields
halt before decrement. The archive now records the consumed original length
prefix and payload; charged cleanup clears output for reuse. Exact work/control
correspondence and the required structural program conditions are proved,
including rejection and absent-input behavior. The complete counted-record
machine now loads the outer count, repeats field calls and restores the original
accepted word. Every raw input halts with exact original-decoder agreement under
a polynomial bound; actual replay-source caches derive that bound from their
hash-query budget. This checks record framing. The source-cache lookup below
derives its typing from internal state; arbitrary raw typed-cache validation
requires a separate execution-interface decision.
A query-preserving comparator now returns full-key equality while restoring the
query and clearing candidate/scratch within 2*|query|+|candidate|+3 transitions.
Its concrete seven-stack layout preserves parser suffix/count/archive, enabling
query reuse. The original cache-entry pair header and key-field parser now
execute before that comparison in one program, preserving the scalar-answer
suffix. All raw prefixes halt with malformed framing distinct from key mismatch;
original typed entries derive the full-key bound. Answer framing is now linked
in the same entry program, preserving match/mismatch and rejecting missing or
trailing data. Its all-input result agrees with the original strict two-field
decoder, and typed entries return the exact encoded answer with a derived bound.
The complete eight-stack lookup now copies the original cache, parses its outer
count and repeatedly extracts and checks entries. It agrees with AList lookup,
retains the query and entire original cache, and derives its transition bound
from actual repaired source states and their n+15 entry bound. Early/late hits,
complete misses and malformed-framing rejection have independent controls.
This result covers internally generated typed caches. It does not claim arbitrary
raw typed-cache decoder agreement. The original framing writer now computes
payload lengths with an executed binary counter, writes the exact length prefix,
retains the destination suffix and clears workspace. Typed key/scalar fields
derive their bounds from the existing codecs. Guarded insertion now executes
lookup and all new entry/count framing in one nine-stack program. It preserves
occupied caches, constructs exact fresh AList insertion, retains both operands
and derives its bound from actual supported source caches. Its cache and sticky
collision-flag projections agree with the original programmed source. The
oracle driver now runs the checked cache routines and preserves the original
request tree, result, cache and ordered miss log for every source program.
Hits consume no entropy; misses request the original challenge before insertion.
The driver now also executes scalar-prefix writing from loaded canonical digits
and chronological log append, keeping both cache and log encoded. The same
eight-stack lookup now parses its actual cached answer, with workspace derived
from the scan and zero distinguished from a miss. The driver consumes those
digits and retains its exact source correspondence. Initial loading, conversion
to input digits, numeric interpretation/range checking, transfers, fuel computation and
continuation execution remain host operations whose machine costs are unproved.
Next implement an
actual operand/continuation execution-cost interface; query-count bounds cannot
discharge that gap. Pinned
VCVio's optional concrete backend has no general oracle compiler/adequacy theorem;
its small canaries and structural ElGamal accounting are not a ready PPT certificate.
Then thread earlier/interleaved attacker queries, trustee proofs and
full election observations. Full adaptive extraction and all-PPT secrecy remain
open. General election-language
and symbolic-to-computational framework work is deferred. Upstream reference
pins/checkouts are preserved. See the latest results-ledger entry for root-build, reference and axiom-audit
evidence. Current migration,
attack, repair, interactive-proof and oracle work is local and has not been committed
or pushed.

## B10 acceptance: historical symbolic ballot secrecy

Claim: swapping the two honest valid ground candidate substitutions in the
actual repaired historical scoped election preserves source weak labelled
bisimilarity. Status: **machine-checked, integrated and audited; B1–B10 complete**.
Formal oracle: scopedVoterElection_ballot_secrecy in
[SourceBallotSecrecy.lean](../../ExplainableCrypto/Helios/Symbolic/SourceBallotSecrecy.lean),
with source_reachable_weak_bisimulation and source_election_weak_bisimilar.
The theorem has arbitrary n (n+1 candidates), arbitrary valid ground candidate
substitutions and arbitrary extra : Nat (extra administration inputs after the
two honest voters). Its only explicit proof hypotheses are Names.Fresh,
NoncesFreshFor each candidate value family and Channels.Fresh. Candidate validity
is carried by CandidateSubstitution. No correspondence, bisimulation, static
observation, target presentation, program-class or normalization premise remains.

Definition audit against the pinned author preprint's Definition 2 (§5.1.2,
printed p. 23), with the already documented finite static-channel source scope:

| Historical obligation | Checked source formulation |
| --- | --- |
| Symmetric relation on closed extended processes | Named.IsWeakLabelledBisimulation.symmetric/closed; closedness follows from actual complete presentations. |
| Static equivalence of full frames | observations uses Named.StaticEq, including both original structural presentations and every public full-E recipe equality. |
| Internal action matched by finite internal closure | internal uses original Named.Reduction and its reflexive-transitive closure WeakReduction. |
| Labelled action with internal prefixes/suffixes | free and bound use original FreeStep/BoundOutput inside WeakFreeStep/WeakBoundOutput. |
| Free variables within the public domain | free retains LabelScoped and the complete original recipe; the constructed source match in fact works for every actual raw input. |
| Fresh bound output | Option.none is fresh; every old handle remains Option.some. Both full targets use the exact outputHandle bijection; SourceElectionRelation.reindex preserves arbitrary common finite handle permutations. |
| Largest relation | WeakLabelledBisimilar is the existential union of witness relations; weakLabelledBisimilar_isWeakLabelledBisimulation proves that union itself satisfies all clauses. |

The full source relation proved in B9 supplies these clauses. Each actual
internal challenge has an actual single-step partner; every public challenge
has an actual partner action with zero surrounding internal steps. Both return
the same successor-preserved relation with actual execution provenance. The
weak formulation permits all finite internal prefixes and suffixes. The final
secrecy theorem instantiates this witness with SourceElectionRelation.initial,
which derives all fields from the actual scoped protocol. The normalized initial
source theorem is a consequence, not a replacement target.

Reality oracle: the existing pinned historical source, equations, source rules,
scoped election and the documented tuple-termination correction. The correction
uses the proper tuple tail test; this is the corrected historical symbolic
claim, not the uncorrected printed guard or a computational security theorem.
No source rule, attacker capability, cryptographic equation, rejection behavior,
nonce policy or upstream pin was changed for B9/B10 closure.

Falsifier and negative control: a live output process and a stopped process have
the same complete static frame but are not WeakLabelledBisimilar. Even arbitrary
silent steps cannot create the stopped process's missing publication channel.
This checked control prevents static equivalence or a stuck witness from standing
in for dynamic secrecy. Other controls instantiate arbitrary administration size,
the reverse voting direction, actual replay input followed by rejection under
the final relation, and missing-domain exclusion. The existing homomorphic,
accepted/rejected ballot, fresh-output, private-channel and local-guard controls
remain. The cyclic semantic-equality reconstruction shortcut and fixing the new
output policy to the old frame policy remain checked counterexamples.
PBT gate: retained independent seeded gates and deterministic controls run in the
main build; this logical assembly adds directed kernel controls and universal
relation proofs, not a new randomized source search. Search failure is not used
as evidence. The only failures in this assembly were redundant simp arguments;
no theorem weakening or trusted definition change was needed.

Integrated evidence: the clean targeted controls and required `lake build`
pass. The final full log contains 4967 standard-only nonempty and 103 axiom-free
reports; the claims checker covers 4058 public theorem entries and 132 current
status documents. Seven changed oleans are current. No holes, custom axioms,
warnings or errors occur in scope; `git diff --check` passes. Eleven public
theorem audits, five controls and five weak-semantics definition audits were
added. Log: `tmp/variable-overlap/source-ballot-secrecy-full-build.log`.

B1–B10 acceptance is complete. No symbolic source-correspondence, action,
frame, freshness or final-secrecy obligation remains open at the stated scope.
The requested [retrospective reuse audit](helios-reuse-retrospective.md) is also
complete: frozen dependency measurements and checked source/CSLib and frame
adapters establish the measured reuse boundary. It is follow-on evidence, not a
premise of this theorem. Computational soundness, concurrent elections and other
protocol extensions remain separate.

The following checkpoint narratives are historical; their open B9/B10 claims
are superseded by the completed theorem and audit above.


## B9 acceptance: one successor-preserved source relation

Status: **machine-checked, integrated and audited; B9 complete**. B10 remains
open. SourceElectionRelation records both actual finite execution histories,
the common reached historical phase, a complete public-handle bijection, shared
base/channel permutations, complete joint source openings and both actual full
frame presentations. Its definition permits either voting order; symm swaps
the complete evidence. It does not assume action correspondence or secrecy.

SourceElectionRelation.staticEq proves actual Named.StaticEq on the original
raw handle domain. SourceFrameReindexing reorders every active provider using
only original parallel laws and existing Mathlib finite-list permutations;
full public-recipe substitution proves the observation transport. The adapter
retains every complete payload and needs a bijection, not an arbitrary map.

SourceElectionRelation.structural and reindex preserve the relation and both
actual executions. internal uses the checked general raw matching theorem;
input preserves the exact original raw recipe after inverse handle transport;
free also excludes old-handle outputs via the reached historical invariant.
bound preserves the same public channel, every old Option.some coordinate and
the fresh Option.none coordinate. Both targets use the same outputHandle
bijection and return the same relation, with extended execution provenance.
Private name policies are retained or jointly refreshed by the existing input
clause. These are actual original-source actions in both directions.

SourceElectionRelation.initial derives every field from the actual scoped
elections, name freshness and the documented nonce/parameter freshness. The
channel-freshness premise is used by matching. The initial theorem assumes no
normalization, presentation, extraction, program class or missing correspondence.
The existing arbitrary-finite-execution frame theorem supplies the independently
checked reachable reconstruction acceptance condition.

Seven new controls retain distinct values under simultaneous handle permutation,
reject a permutation applied to only one observation frame, construct actual
initial membership, preserve one relation through a real replay input followed
by rejection, preserve a nonidentity reached-handle permutation, and exclude an
unexported initial domain. Existing actual fresh-publication, local guard,
private-channel, cyclic, rejection and cryptographic controls remain integrated.
No new random Structural campaign or upstream build is claimed. Failures were
proof engineering: finite-list theorem qualification, identity function reduction,
explicit Fin numeral types and use of finCongr rather than a generic type cast.

Integrated evidence: the targeted controls and required `lake build` pass.
The full log contains 4951 standard-only nonempty and 103 axiom-free reports;
the claim checker covers 4047 public theorem entries and 132 current-status
documents. Five changed oleans are current, all 1646 local links resolve, and
no holes, custom axioms, warnings or errors occur in scope. `git diff --check`
passes. Twenty-three public theorem audits, seven controls and two definition
audits were added. Log: `tmp/variable-overlap/source-election-relation-full-build.log`.

Remaining B10 acceptance obligations:

1. **Open — source_reachable_weak_bisimulation.** Package the completed
   SourceElectionRelation clauses as one symmetric source weak labelled
   bisimulation. Use actual Named.StaticEq, original Reduction/FreeStep/
   BoundOutput and finite internal closures. Keep full label domains and the
   typed fresh output coordinate explicit. Check this definition against the
   historical Definition 2; no conditional correspondence premise is needed.
2. **Open — source_election_weak_bisimilar and
   scopedVoterElection_ballot_secrecy.** Instantiate that relation with the
   actual scoped initial elections using SourceElectionRelation.initial and
   documented name, nonce/parameter and channel freshness. Quantify arbitrary
   valid ground candidates, positive candidate count and finite administration
   size. Retain full E/E0 observations, rejection and independent positive and
   negative controls; run the public theorem, full build and writing audits.

The retrospective reuse audit remains after B1–B10 secrecy completion.

The following checkpoint narratives are historical and do not reopen B9.


## Actual raw internal availability and matching

Status: **machine-checked, integrated and audited** for general raw internal
availability and each reached internal matching clause. B9's combined relation
and B10 remain open.

SourceReadyPrefixExtraction derives actual ready input/output prefixes under
original finite local scopes. SourceCommunicationAvailability extracts both
compatible heads from the same raw process, retains the untouched context and
uses the original message_communication derivation. Its Named version retains
all private restrictions. SourceRawCommunicationMatching proves the intermediate
non-check phase result; its explicit conditional exclusion is now removed by
SourceRawInternalMatching.source_reachable_internal_match.

The conditional gap closes without changing the ground-guard reduction rules.
SourceLocalCodePrefix.exists_local_code_prefix extracts all existing local scopes,
provider forest and full live code from arbitrary original Extended syntax.
SourceOpenLocalPresentation.BinderStructural.open_local_frame uses the completed
actual output-presentation theorem to derive a full presentation after opening
one existing local. The auxiliary output is proof instrumentation, not an action
inserted into the historical protocol. SourcePresentedInternalAvailability then
opens that finite prefix inductively. At the binder-free leaf, the actual frame
path rewrites the retained providers beside unchanged code; activeFrame_apply
grounds the code, including guards and both continuations. Full EvalEq transports
the given internal Tau, tau_ground_derivable produces the original reduction,
and exact inverse variable bijections reclose all original local/name scopes.

Extended.internal_available_of_presentation requires only an actual current
frame presentation, a complete realization and its internal Tau. The named
JointOpening.internal_available requires only the actual current presentation,
full joint opening and canonical Tau. Prefix, forest, opened presentations and
guard grounding are derived. Fresh canonical name permutations are bijections,
so both positive and negative guards transport. source_reachable_internal_match
uses this availability together with the reached phase invariant and checked
phase determinism; both raw successors retain complete presentations and full
static equivalence at the same exact handle cast. No check-phase, extraction,
normalization, target presentation or missing-correspondence callback remains.

Seven directed controls include a local guard compared against a dependent
public provider in both truth directions, distinct then/else output channels,
communication across two separate local scopes, private raw communication,
mismatched-channel impossibility, the retained cyclic presentation exclusion,
and actual historical component-replay rejection with a padded raw partner and
full successor observations in both voting directions. Existing nested-prefix,
private-output and cryptographic positive/negative controls remain. No new
random Structural search or new historical-model validation is claimed.

Failures were proof engineering: dependent local-variable types needed explicit
renaming identities, frame rewrites needed their actual structural theorem, and
finite casts needed explicit target types. A fixture's proposed intermediate
syntactic equality omitted substitution of its retained public provider; it was
false at that intermediate point. The correction applies existing activeFrame_apply
before asserting the independently specified ground guard. The public theorem
and all source rules remain unchanged. The semantic-equality-only structural
shortcut and fixed-old-policy output shortcut remain refuted.

Integrated evidence: `lake build` succeeds; the clean targeted control build
also succeeds. The current full log contains 4926 standard-only nonempty and
103 axiom-free reports. The claims checker covers 4024 public theorem entries
and 132 current-status documents. Ten changed Lean oleans are current; all 1684
local links resolve. No holes, custom axioms, warnings or errors were found in
scope; `git diff --check` passes. Twenty-seven public theorem audits include
seven controls, with both guard truth values quantified. Log:
`tmp/variable-overlap/source-raw-internal-full-build.log`.

Remaining B9/B10 acceptance obligations:

1. **Open — integrate all clauses into one source relation.** The individual
   source_reachable_internal_match, source_reachable_input_match and
   source_reachable_bound_match clauses are now checked. Package their current
   phase, actual execution provenance, full presentations and shared handle/name
   coordinates, and prove the same relation at every pair of actual successors.
   Cover structural changes, internal reductions, unchanged public input labels,
   fresh outputs, reindexing and both voting directions. Preserve old-handle
   output exclusion and rejection. Intended declarations: SourceElectionRelation
   with structural, internal, free, bound and reindex closure; its initial scoped
   membership must derive all fields from the documented freshness conditions.
2. **Open — source_reachable_weak_bisimulation and
   source_election_weak_bisimilar.** Assemble the source-level weak labelled
   bisimulation from the completed B9 relation. The observations must be actual
   full Named.StaticEq presentations and actions must use the original Named
   semantics, with exact fresh output domains. Prove symmetry and preservation;
   do not assume correspondence at this interface.
3. **Open — scopedVoterElection_ballot_secrecy.** Transfer to the actual scoped
   elections with documented name, nonce/parameter and channel freshness,
   arbitrary valid ground candidates and finite administration size. Audit the
   full E/E0 observations, rejection, public hypotheses and independent controls.
   Stage matching, equal tallies and static equivalence alone are insufficient.

The retrospective reuse audit stays after B1–B10 secrecy completion.

The following checkpoint narratives are historical; their next-step prose is
superseded by the current dependency map above.


## Actual raw input and bound-output matching

Status: **machine-checked, integrated and audited** for B9's visible action
availability and successor matching. B9 internal matching and B10 remain open.

SourceVisibleReadiness defines HasInput and HasOutput only at evaluation depth.
Substitution and full EvalEq preserve those ready prefixes; arbitrary name maps
preserve readiness at the mapped channel. The original source input rule and
message_output derivation then supply real Extended actions under arbitrary
parallel and local-variable contexts. The full raw input recipe is shifted
correctly under each local binder, and bound output keeps the complete payload
and exports one fresh Option coordinate. No guard is crossed and no action rule
is added.

SourceJointVisibleAvailability lifts these results to Named.JointOpening through
an actual fresh full name opening. JointOpening.input_available constructs an
actual input on the raw process with the unchanged recipe; allocation freshness
is derived against every name in that label and the raw process. The theorem
requires a public channel and a ready canonical prefix. It allows any raw
recipe for action existence; matching its canonical evaluated successor uses
the separate public-recipe premise, as the existing public_input_target requires.
JointOpening.bound_available similarly constructs an actual raw bound output
on the same public channel, preserving the full restriction prefix. Neither
requires a target presentation or an assumption of action correspondence.

SourceRawInputMatching.source_reachable_input_match combines actual current
presentations and the existing coordinated fresh-input classification with the
new raw-partner action. Both actual successors have reached phases, full
presentations at jointly refreshed policies and Named.StaticEq observations.
The exact original recipe remains in the partner's action label, even when it
contains a formerly private spelling. SourceRawOutputMatching.
source_reachable_bound_match uses the actual publication and checked stage swap
only to identify the partner's enabled output, then constructs that output in
the raw partner itself. Output target closure, constructive presentation and
phase alignment preserve both full frames under the same Option/outputHandle/
Fin.cast domain bijection. Static equivalence covers every handle there; it does
not replace matching.

Eight directed controls cover full-SPK input labels, fresh output domains,
prefix-blocked nested actions, wrong channels, private ready inputs/outputs that
cannot escape, a real formerly-private-literal input from nonidentity name
coordinates with a padded raw partner, and actual ballot publication with a
statically equivalent full raw-partner successor in both voting directions.
Expected ready/blocked channels come directly from literal syntax. The historical
independent cryptographic, rejection, cyclic and policy controls remain intact.
No new randomized campaign over source Structural derivations is claimed.

Failures were proof engineering: readiness predicates needed explicit reduction
for a concrete decision; unused parallel-equivalence hypotheses polluted a local
induction; dependent phase domains required explicit whole-process cast identities;
and the Reachable alias needed a type annotation to select its swap theorem.
The statements and original model assumptions were retained.

Integrated evidence: `lake build` succeeds (4118 jobs); the clean targeted
control build succeeds (1468 jobs). The current full log contains 4899
standard-only nonempty and 103 axiom-free reports. The claims checker covers
3997 public theorem entries and 132 current-status documents. Seven changed Lean
oleans are current, and all 1684 local links resolve. No holes, custom axioms,
warnings or errors were found in scope; `git diff --check` passes. Twenty-eight
public theorem audits, eight controls and two readiness-definition checks were
added. Log: `tmp/variable-overlap/source-raw-visible-full-build.log`.

Remaining B9/B10 acceptance obligations:

1. **Open — actual raw internal availability and source_reachable_internal_match.**
   For an enabled historical internal phase, construct an actual reduction or
   the required weak internal sequence from the related raw partner. Communication
   needs two compatible ready prefixes in that same raw state, including
   interleaved local scopes. A conditional additionally needs an actual ground
   guard before original thenBranch/elseBranch can apply. Current forward
   interpretation and conditional-location theorems do not supply this converse.
   The new visible readiness lemmas establish separate input/output existence,
   not a common communication redex or a valid conditional action.
2. **Open — integrate all clauses into one source relation.** Retain actual
   execution provenance, the shared reached phase/name coordinates, full frame
   presentations and complete handle bijections. The input and bound-output
   successor clauses are now checked in source_reachable_input_match and
   source_reachable_bound_match. Add internal closure and symmetric matching;
   retain old-handle output exclusion, rejection and freshness. B9 is complete
   only when these acceptance conditions all hold together.
3. **Open — source_reachable_weak_bisimulation and
   source_election_weak_bisimilar.** Assemble the source-level weak labelled
   bisimulation from the completed B9 relation, with actual Named.StaticEq
   observations and the original action semantics.
4. **Open — scopedVoterElection_ballot_secrecy.** Transfer to the actual scoped
   elections with documented freshness, arbitrary valid ground parameters and
   arbitrary finite administration size. Audit public hypotheses, full E/E0
   observations and independent controls. Do not assume the remaining
   correspondence or report stage matching/static equivalence as secrecy.

The retrospective reuse audit stays after B1–B10 secrecy completion.

Concrete next obstruction: SourceExtendedSyntax.Reduction.thenBranch and
elseBranch require a syntactically ground Formula embedded into the raw variable
context. A semantic realization of a ready branch does not itself satisfy that
constructor. The checked current frame presentation supplies actual provider
constraints, but a derivation must use them to ground the ready guard while
retaining its continuations and all providers. Compare that focused guard
rewrite with whole-live-code normalization before adding a larger layer. The
new visible proofs show that whole-live-code normalization was unnecessary for
input and output; no such premise was added. Internal communication separately
needs a simultaneous prefix-extraction argument. These are proof obligations,
not new attacker restrictions, source rules or supplied invariants.

The following checkpoint narratives are historical; their next-step prose is
superseded by the current dependency map above.

Implementation locations: SourceVisibleReadiness, SourceJointVisibleAvailability,
SourceRawInputMatching, SourceRawOutputMatching and SourceRawVisibleSPOT. All five
are imported into the main build and covered by Audit/the claims checker. The
verification script is tmp/variable-overlap/verify-source-raw-visible.py. The
previous reachable-frame checkpoint remains integrated. All build sessions are
terminal. No upstream pins, Lake reference dependencies or protocol definitions
changed. No agents or commits/push were used.


## Actual reachable source frame presentation

Status: **machine-checked, integrated and audited** for B9 reachable-state frame
reconstruction. B9 action matching and B10 remain open.

source_reachable_frame_presentation now gives every finite original execution
from scopedVoterElection a reached phase, refreshed name permutations, a complete
handle bijection and an actual RepresentsFrame witness at the exact phase policy
and full sourceView. Its premises are the actual execution, documented ns.Fresh,
left/right NoncesFreshFor and ch.Fresh. Candidate validity remains encoded by
CandidateSubstitution. There is no caller-supplied program class, target
presentation, model environment, elimination order or correspondence hypothesis.

The new fresh-output branch first derives actual CapturedEq congruence, including
selected occurrences and every SPK field. Its quotient environment satisfies the
extracted provider forest by its own retained provider equations. Quotient
exactness and BoundOutput.opened_algebra_values then yield an actual captured
structural equality with a derived ground term. captureCopy_structural preserves
any uniquely defined frame exporting the selected handle, including cyclic
payloads and nested locals; its recursive measure ignores payload size and is
preserved by the original binder renaming. CapturedEq.ground_reclose combines
this identity with the old actual reclosure. BoundOutput.opened_frame_presentation
returns the complete ground target under the exact outputHandle bijection.
BoundOutput.exists_frame_presentation recloses every name from an actual fresh
opening and normalizes its exact base/channel sets to an existential policy.
CoordinatedPhaseOpening.presented applies the already checked alignment theorem.
Named.Execution.election_presented_phase covers all original execution
constructors; the source theorem supplies its initial witnesses.

Fifteen controls cover retained providers, selective context holes versus
simultaneous substitution, the fourth SPK field, nontrivial quotient values,
cycles that cannot gain arbitrary ground captures, two dependent local binders,
a freshly opened private output and its independently expected value, copy
preservation of a cycle, full private policy reconstruction from an empty old
policy, rejection of that old empty policy as a target policy, and an actual
mixed historical run ending in replay rejection in either voting world.
No new randomized campaign over Structural is claimed. Universal proofs cover
constructors/contexts/finite executions; the directed controls test the stated
boundaries. The historical independent cryptographic controls remain imported.

Failures in this increment were proof engineering: a noncomputable simultaneous
substitution needed simplification before a concrete inequality could be decided;
recursive binder renaming needed an explicit varying type parameter and a
syntax-size termination proof; dependent policy indices required exposing the
frame representation during identity simplification. No candidate was weakened,
no source rule or cryptographic assumption was added, and both earlier checked
counterexamples remain decisive boundaries.

Integrated evidence: `lake build` succeeds (4113 jobs); the clean targeted
control build succeeds (1474 jobs). The current full log contains 4869
standard-only nonempty and 103 axiom-free reports. The claims checker covers
3969 public theorem entries and 132 current-status documents. Nine changed Lean
oleans are current, and all 1684 local links resolve. No holes, custom axioms,
warnings or errors were found in scope; `git diff --check` passes. Forty-six
public theorem audits, fifteen controls and five definition checks were added.
Log: `tmp/variable-overlap/source-reachable-frame-presentation-full-build.log`.

Remaining B9/B10 acceptance obligations:

1. **Open — actual raw-partner action availability.** Given the maintained
   reachable source relation and a corresponding evaluated phase action, derive
   a real action (or the required internal weak sequence) from the other raw
   source state. The new frame presentation theorem supplies observations and
   provider equations; it does not reconstruct live code or supply an action.
   Inspect existing realization/interpretation and canonical action derivations
   for the precise missing converse before adding machinery.
2. **Open — source_reachable_internal_match, source_reachable_input_match and
   source_reachable_bound_match.** Use availability and existing phase matching
   to retain both actual successors in one relation. Preserve exact old/fresh
   handle domains, jointly refreshed private policies, unchanged public input
   recipes, output freshness, acceptance and stop-on-rejection behavior. The
   existing common-input result constructs a canonical partner action only.
3. **Open — source_reachable_weak_bisimulation and
   source_election_weak_bisimilar.** Assemble symmetric internal/free/bound action
   clauses and actual Named.StaticEq observations after B9 acceptance closes.
4. **Open — scopedVoterElection_ballot_secrecy.** Transfer the bisimulation to
   the actual scoped elections with documented freshness, arbitrary valid ground
   parameters and arbitrary finite administration size. Audit public hypotheses,
   full E/E0 observations and independently derived controls; no missing
   correspondence may become a final theorem premise.

The retrospective reuse audit remains after B1–B10 secrecy completion.

The following checkpoint narratives are historical; their next-step prose is
superseded by the current dependency map above.


Focused next action obligation after inspecting source rules: prove
Named.JointOpening.input_available and Named.JointOpening.bound_available for
an enabled public phase action, then use the existing coordinated target lemmas
to classify the actual raw successors. These names are planned, not checked.
SourceAtomicLabels.FreeStep.input and SourceAtomicOutput.message_output accept
raw payload syntax, so input/output availability should need exposed source
prefixes and fresh name openings rather than normalization of every live-code
payload. SourceEvaluatedEquivalence preserves prefix behavior, and the existing
Visible inversion/parallel lemmas expose those prefixes. Construct exact input
recipes and fresh output coordinates through local and name scopes. Directed
controls must include a ready public prefix, a prefix blocked underneath another
input/output, and a private channel that cannot be exported as a public action.
Internal communication then needs two compatible ready prefixes. Conditional
availability separately requires the actual guard decision in its provider
context; the existing forward conditional-location result does not prove it.
This is the next concrete boundary to close before building a larger live-code
normalization layer. No new source abstraction has been added for it.

Current implementation locations: SourceCapturedEquations,
SourceCaptureAlgebra, SourceCaptureCopy, SourceOutputFramePresentation and
SourceReachableFramePresentation. Controls are SourceCapturedEquationsSPOT and
SourceOutputFramePresentationSPOT. All seven modules are imported by the main
build and covered by Audit and the claims checker. Full-build and verification
logs use the source-reachable-frame-presentation prefix in tmp/variable-overlap.

Maintain the existing task/blueprint/results workflow. No new backlog, agents,
framework migration, reference Lake dependencies, commits/push or upstream pin
changes. The next proof must construct actions from the actual raw partner.


Latest completed obligation: derive a ground witness and old/fresh algebraic
values for an actual output from its old presentation and actual reclosure.
B9 target Structural presentation and raw-partner matching, and B10, remain open.

SourceFrameAlgebra supplies arbitrary full-E term models and all-rule frame
satisfaction/hidden-value uniqueness preservation. Its actual-source endpoints
are RepresentsFrame.opening_algebra_rigid, BoundOutput.opened_value_unique and
BoundOutput.opened_algebra_values. The last theorem derives f, a ground m, an
original ground solution, and the corresponding old/fresh values in every model.
SourceFrameAlgebraQuotient.ofTermCongruence supplies the quotient model constructor;
fullGround and eleven SPOT controls establish nontriviality and the intended
source/alias/name-opening boundaries. Ordinary ground-only rigidity is not used
as a substitute for actual structural reconstruction.

Integrated evidence: `lake build` succeeds (4106 jobs); the clean targeted
control build succeeds (1408 jobs). The current full log contains 4820
standard-only nonempty and 101 axiom-free reports. The claims checker covers
3923 public theorem entries and 132 current-status documents. Five changed Lean
oleans are current, and all 1684 local links resolve. No holes, custom axioms,
warnings or errors were found in scope; `git diff --check` passes. Forty public
theorem audits, eleven controls and seven definition checks were added. The
algebra/quotient definitions are proof instrumentation, with no new source rule,
execution relation or cryptographic assumption.
Log: `tmp/variable-overlap/source-frame-algebra-full-build.log`.

Remaining fresh-output work, all still **conjectured** unless stated checked:

1. Define Extended.CapturedEq by an actual Structural path between the same
   frame with a fresh active observer of two terms. Prove full-E inclusion,
   provider equations and congruence under term contexts. In particular, derive
   contextual congruence using actual local aliases; simultaneous Subst cannot
   simply be treated as rewriting one chosen occurrence.
2. Use the checked complete provider forest to instantiate the checked
   FrameAlgebra.ofTermCongruence constructor with CapturedEq. Derive its actual
   model solution from the provider equations and existing variable-prefix
   coordinates. Apply checked BoundOutput.opened_algebra_values and quotient
   exactness to obtain a captured-term Structural equality with the ground value.
3. Derive the fresh alias/copy and reclosure bridge that turns this equality,
   together with the actual old-frame reclosure path, into a complete target
   presentation. Reclose the actual full name prefix and preserve Option/
   outputHandle coordinates. Its private policy is existential at this step;
   the checked same-old-policy counterexample still forbids fixing it prematurely.
4. Finish Named.BoundOutput.exists_frame_presentation, then apply checked
   JointOpening.align_presentation to the full reached-phase witness and close
   source_reachable_frame_presentation. Actual raw-partner internal/input/bound
   matching and B10 bisimilarity/secrecy remain subsequent obligations.

The algebraic route avoids assuming an elimination order for the finite forest.
Its extra strength is derived from actual structural provenance. It does not
infer structural presentation from semantic equality or ground-only rigidity.
The actual capture congruence and reclosure bridges must still be proved; no
premise asserting either may enter the final secrecy theorem.

Proposed next proof shape (unproved engineering notes): for a finite provider
forest f : Extended W, let CapturedEq f r s mean the original Structural path
between par (f.rename some) (active none (shiftTerm r)) and the same context
capturing s. Reflexivity/symmetry/transitivity are immediate; full-E inclusion
uses Rewrite. Provider equations can use FrameForest.extract_provider and
SubstActive on the distinct fresh observer. Contextual congruence needs an actual
fresh local alias so only the chosen term occurrence changes. A useful route is
to treat an existing capture equality as an equality of local providers, place
the contextual observer beside it, and apply let_normalize on both endpoints.
Do not assume selective occurrence substitution from the global Subst rule.

After congruence, ofTermCongruence applies to that exact Structural relation.
Assign each opened forest variable its own quotient class; provider equations
then give its model solution. Reclose the finite variable prefix using the
outerVar coordinates and transfer through its existing Structural path before
applying opened_algebra_values. Quotient exactness should give the fresh captured
variable's equality to a ground term as an actual Structural path. To finish,
a fresh alias/copy must exchange the observed handle with the existing exported
handle, hide the old copy, and use actual output reclosure to normalize the old
frame. Keep the actual complete name prefix until phase-policy alignment.
All of these bridges remain to be proved; none is a source action or an axiom.

Implementation notes: make the model parameter explicit in recursive Satisfies
and Rigid definitions. Quotient record eval_eq uses explicit intros for implicit
term binders. In source fixtures retain exact groundTerm/groundAgent embeddings.
The source algebra imports current actual-presentation proofs; no original
source definition or equation was changed. All sessions are terminal.

Maintain task list.md and the existing blueprint/results/source record. No new
backlog, agents, framework migration, Lake reference dependency, commits/push or
upstream pin changes. Retrospective reuse remains after the secrecy milestone.
The following sections are preceding checked checkpoints.


Latest completed obligation: finite complete provider extraction from every
actual scoped-election execution, with exact phase handles, fresh name allocation
and actual frame Structural evidence. Ground presentation and B9/B10 remain open.

SourceVariableFramePrefix adds universal frame-only variable hoisting, explicit
outer-variable embedding, complete local/public provider extraction and an actual
path exposing any chosen provider. UniqueDefinitions already requires each local
binder to have its own definition. SourceReachableFramePrefix proves this and
complete public coverage across all original Execution constructors, then
scopedVoterElection_execution_frame_prefix combines it with the full reached
phase and handle-domain theorem. The current-state presentation and program
extraction are not caller premises of this historical extraction theorem.
SourceVariableFramePrefixSPOT supplies seven directed checked controls.

Integrated evidence: `lake build` succeeds (4103 jobs); the clean targeted
control build succeeds (1461 jobs). The current full log contains 4773
standard-only nonempty and 101 axiom-free reports. The claims checker covers
3883 public theorem entries and 132 current-status documents. Five changed Lean
oleans are current, and 1684 local links resolve. No holes, custom axioms,
warnings or errors were found in scope; `git diff --check` passes. Twenty public
theorem audits, seven controls and five definition checks were added. The new
definitions describe variable-prefix notation and a frame-syntax predicate;
no operational rule or execution relation was added.
Log: `tmp/variable-overlap/source-variable-frame-prefix-full-build.log`.

The next missing proof is still Named.BoundOutput.exists_frame_presentation:
use actual current presentation and output provenance to eliminate the extracted
local provider system and produce some complete ground target presentation.
Finite-forest extraction now supplies syntax, freshness, unique providers and
all coordinates; it does not supply an elimination order or ground-valued
structural path. Neither unique definitions, local rigidity nor semantic
realization equality may be silently substituted for that proof. Once it is
constructed, checked JointOpening.align_presentation recovers the exact phase
policy and values. Then complete source_reachable_frame_presentation, actual
raw-partner internal/input/bound matching, and B10 bisimilarity/secrecy.

Engineering notes: LocalVars is a recursive type family; unfold it before finite
Option case analysis. Within BoundOutput theorem statements qualify
Named.restrictNames to avoid resolving the action's method of the same name.
In FrameForest.frameOf proofs qualify Extended.frameOf. Original Named/Extended
structural constructors supply every normalizing path; there is no new source
action, execution relation or crypto equation. All sessions are terminal.

Keep task list.md, blueprint/results and existing source record current. No new
backlog, agents, framework migration, Lake reference dependency, commits/push or
upstream pin changes. Retrospective reuse remains after the secrecy milestone.
The following sections are prior checked checkpoints.


Latest completed obligation: policy/value alignment of an already extracted
actual frame presentation with the reached canonical phase. B9 fresh-output
extraction and actual partner matching, and B10 source secrecy, remain open.

SourcePresentationAlignment supplies seven checked public lemmas, ending in
JointOpening.align_presentation. Its necessary premise is some actual target
presentation; the full JointOpening alone does not supply one. The proof
extracts actual opened ground frames on both sides, identifies their values
under full E, and recloses a BinderStructural path with derived freshness.
Five SourcePresentationAlignmentSPOT controls retain both counterexample
boundaries and exercise actual capture with a different starting policy.

Integrated evidence: `lake build` succeeds (4100 jobs), including all five
new controls. The clean targeted control build succeeds (1403 jobs). The current
full log contains 4757 standard-only nonempty and 92 axiom-free reports; the
claims checker covers 3863 public theorem entries and 132 current-status
documents. Four changed Lean oleans are current, and all 1684 local links resolve.
No holes, custom axioms, warnings or errors were found in scope; `git diff
--check` passes. Twelve public theorem audits were added. No operational rule,
execution relation or cryptographic assumption was added.
Log: `tmp/variable-overlap/source-presentation-alignment-full-build.log`.

NEXT: constructive existence of a complete presentation for arbitrary actual
fresh-output targets, intended Named.BoundOutput.exists_frame_presentation.
Current presentation plus actual output should yield existential target policies
and ground values; this candidate is unproved. Track dependent local providers
through original structural derivations, with exact Option/outputHandle domains.
After existence, apply checked alignment with source_coordinated_output_next's
full phase witness; finish source_reachable_frame_presentation. Then construct
actual raw-partner matches and assemble/audit source secrecy. Do not add another
program class, assume semantic reconstruction, or impose the old frame's private
policy on the output. Both checked counterexamples remain load-bearing.
The blueprint's first table and task list.md are the authoritative dependency
map. Upstream pins and checkouts remain untouched; retrospective reuse stays
after the secrecy milestone. No sessions remain running after verification.

The following branch descriptions are the preceding checked checkpoint.


Latest completed branches: actual presentation preservation through historical
internal steps and arbitrary inputs. Fresh-output presentation and B9/B10 remain
open. Full finite source execution phase tracking remains checked.

SourceInputPresentationClosure supplies:
- RepresentsFrame.transport_state_structure and cast_mapped_handles.
- JointOpening.common_fresh_input_presented: actual whole-state freshening
  transports both old presentations; FreeStep.frameOf presents the raw target.
- source_coordinated_internal_presented_next: reached next phase, exact handle
  cast, full joint witness and actual target presentation.
- source_coordinated_input_presented_next: all freshness/classification derived,
  target phase, raw target and partner presentations at the new common policy,
  the partner's refreshed JointOpening and their actual static-equivalence.
  The partner has not performed its matching input; do not claim paired closure.

Five SourceInputPresentationSPOT controls cover actual historical input and
replay rejection, a currently private literal forcing actual key freshening,
rejected stale policy and the rejected generic output route.
SourceFrameCompatibilitySPOT adds eight controls: latentPrivateOutput has a
private atom 40 used only by its live output. Its old frame and output reclosure
admit empty base policy, but latentPrivateTarget has no such presentation for
any value or hidden channels. Keeping {40} supplies a full target presentation.
This refutes a generic frame-only same-policy output lemma. It does not refute
the historical reachable theorem, which retains full process/phase provenance.

Integrated evidence: `lake build` succeeds (4098 jobs); targeted controls
succeed (1458 jobs). The current log has 4745 standard-only nonempty and 92
axiom-free reports. The checker covers 3851 public theorem entries and 132
current-status documents. Five changed Lean oleans are current; 1684 local
links resolve. No holes, custom axioms, warnings or errors were found in scope;
`git diff --check` passes. This increment adds 18 public theorem audits,
including 13 controls, with no new operational rule or execution relation.
Log: `tmp/variable-overlap/source-input-presentation-full-build.log`.

NEXT: the fresh-output branch of source_reachable_frame_presentation. Use actual
source presentation plus full phase/process provenance. Name openings and the
checked structural reconstruction criterion may isolate the local-variable
extraction obligation, but require actual BinderStructural evidence. Do not
infer it from SameRealizations, local rigidity or reclosure. Do not substitute
another convenient program class for arbitrary reachable raw targets.
Then close actual raw-partner internal/input/bound matches and B10 source weak
labelled bisimilarity plus scopedVoterElection_ballot_secrecy. Planned declaration
names and their precise status/dependencies are in the blueprint's first table.

Engineering notes: private-policy indices on Frame are phantom but their
restrictionNames use is not. When composing mapped policies, unfold
RepresentsFrame/canonicalFrame/activeFrame to expose those sets before simp.
Use transport_state_structure for identity-mapped presentations to avoid
unnecessary dependent Frame coercions. All final proofs have no holes/axioms.

Maintain task list.md, blueprint/results and existing model docs. No new backlog,
no agents, commits/push, framework migrations, Lake reference dependencies or
upstream pin changes. Post-secrecy reuse retrospective remains deferred.

## Historical checkpoints

### Full reachable phase checkpoint

Latest completed obligation: phase correspondence across every original finite
source execution, starting from scopedVoterElection. B9/B10 remain open.

SourceReachableElectionPhases:
- Named.Execution.election_phase retains a reached phase, name coordinates and
  an explicit bijection V ≃ Fin phase.handles for the actual raw target.
- scopedVoterElection_execution_phase supplies initial structural extraction.
- exists_scoped_execution_phase discharges parameter/nonce freshness with the
  existing allocator for arbitrary valid ground parameters.
- scopedVoterElection_execution_no_handle_output closes that case for every
  actually reached raw state, without a caller-supplied phase witness.

The existing heterogeneous Named.Execution is reused unchanged. Internal and
free actions retain the handle bijection; arbitrary input refreshes e/k through
source_coordinated_common_input_next paired with the same source. Bound output
uses optionCongr i, outputHandle and finCongr of the next-domain equality.
Reindex composes the inverse handle bijection. SourceExecutionHandleRenaming
contains six original-action bijection lemmas and the Extended swap helper.
No new operational abstraction or definition was added.

Thirteen SourceReachableElectionSPOT controls include two actual publications
from the scoped election, replay input/rejection, blocked next public input,
handle exchange, actual renamed input and fresh/old domain distinction. The
inhabited semantic-only reconstruction counterexample is retained.

Integrated evidence: `lake build` succeeds (4096 jobs); the targeted control
build succeeds (1454 jobs). The current full log contains 4727 standard-only
nonempty and 92 axiom-free reports. The checker covers 3833 public theorem
entries and 132 current-status documents. Five changed Lean oleans are current;
1683 local links resolve. No holes, custom axioms, warnings or errors were found
in scope; `git diff --check` passes. This increment adds 24 public theorem
audits, including 13 controls, and no new definition or operational rule.
Log: `tmp/variable-overlap/source-reachable-election-full-build.log`.

NEXT: source_reachable_frame_presentation for arbitrary actual reachable targets,
then source_reachable_internal_match, source_reachable_input_match and
source_reachable_bound_match with successors in one actual matching relation.
The exact status/dependency map is near the top of the blueprint. JointOpening
plus provenance now tracks phases, but no theorem promotes realization equality
or rigidity to structure. Scoped-program capture results still have syntax and
freshness premises that cannot be assumed for arbitrary structural detours.
Initial scoped-voter normalization is already proved; additional program classes
are not the gap. Classify any failed reconstruction claim before adding machinery.
B10 weak labelled bisimilarity and scopedVoterElection_ballot_secrecy remain
unproved; their statements must not assume the missing B9 correspondence.

Maintain task list.md, blueprint/results and existing model documents. No new
backlog. No agents authorized. No commits/push, framework migration, Lake
reference dependency or upstream pin changes. The reuse retrospective is after
secrecy. Pinned research skills and workflow remain applicable.



### Structural opening checkpoint

Latest frontier: [structural action openings](helios-source-structural-openings.md).
All paired action openings retain BinderStructural endpoint paths. Actual Named
structural equivalence is characterized by jointly fresh binder-structural
openings, including unequal allocation lists. B9/B10 remain open at 8/10.

SourcePairedOpeningReduction and SourcePairedVisibleOpenings now use
transport_binder_opening in their single core opening_binder_step proofs.
Old opening_step interfaces project sameRealizations. Internal reduction keeps
its existential finite needed-support set; visible labels and Option targets
remain exact. SourceStructuralActionOpenings derives three opening_named_step
results by Named congr over the actual embedded Extended action.

SourceStructuralOpeningReconstruction proves reclosed_freeNames_subset,
Opens.structural_of_binder, Structural.fresh_binder_openings and
structural_iff_fresh_binder_openings. Freshness avoids both original allNames
sets. Add unused outer prefixes, compare bodies under the common prefix,
reorder, remove added prefixes and compose actual opening paths. Different
lengths and actual used binders are supported. There is no new relation/rule.

Fifteen SourceStructuralOpeningSPOT controls pass, covering dependent binder
exchange, different prefixes, used alpha conversion, complete SPK-labelled
input, scoped fresh output and internal communication. Dropping freshness lets
a private input share the public body but their channel sets prohibit structure.
The inhabited cycle remains a counterexample to semantic-only reconstruction.

Next: derive structural body evidence for arbitrary reachable raw targets,
using the strengthened action interface. The characterization still requires
BinderStructural; neither SameRealizations nor rigidity supplies it. General
raw matching, output-frame presentation and final bisimulation/secrecy remain
open. Program/scoped capture normalization, execution rigidity and the old-handle
election case remain checked under their existing hypotheses.

Integrated verification: `lake build` passes **4093 jobs**; targeted controls
pass **1394 jobs**. The current log reports **4703** nonempty standard-only and
**92** axiom-free results. The claim audit covers **3809** public theorem entries
and **132** current-status documents. All seven changed Lean sources have current
oleans; **1686** local links resolve. No proof holes, custom axioms, warnings or
errors were found in the checked scope; `git diff --check` passes. This increment
adds **25** theorem audits, including **15** public kernel controls, with no new
definition or operational rule.
Log: `tmp/variable-overlap/source-structural-opening-full-build.log`.

Maintain the [blueprint](helios-proof-blueprint.md), B9/B10 item in
[task list.md](../../task%20list.md), [results](helios-results.md) and model docs.
For the public workflow, read [workflow.md](workflow.md). Local paper:
tmp/cortier-smyth-layout.txt. No subagents authorized; upstream pins unchanged.



### Scoped program-capture checkpoint

Latest frontier: [scoped program captures](helios-source-scoped-capture.md)
retains actual output targets through interleaved base-name/local scopes and
reconstructs full Named frames with the complete combined private policy.
B9/B10 remain open at 8/10 milestones.

SourceScopedProgramCapture adds ScopedTermProgram.capture to the existing
datatype. compile_output_capture derives exact raw targets with no Hoistable
premise. capture_hoist uses existing Hoistable; capture_normalizes then eliminates
dependent locals in the erased program. No operational rule or new program type.

SourceScopedCaptureFrames: scoped_program_prefix_policy identifies old prefix
plus program names with restrictionNames hidden (restricted union names.toFinset).
It supports duplicates via existing source prefix reordering/deduplication.
frame_scoped_program_capture_normalize requires program.Hoistable and every
program name absent from the full old frame.nameSupport. This permits old-frame
extrusion and the full computed capture under outputHandle. The restricted
normalize/represents theorems give actual full Named presentations at the combined
private policy. restricted_scoped_program_output supplies the actual action and
complete target, also requiring channel not hidden. This is not policy padding.

Twenty-two SourceScopedCaptureSPOT controls retain a literal target with private
50 between two dependent locals and private 51 inside both, the complete three
handle values and policy {40,50,51}, real static observations/outputs, failed
provider/name freshness with original output still available, repeated name
[50,50] and base/channel sort separation. E-distinct 51/52 is a fixed-coordinate
control, not a prohibition of alpha conversion. Omitting program policy names
wrongly admits a literal nonce; the exported handle remains a public recipe.

Next: extract solvable forms from arbitrary reachable structural representatives,
including ones outside these syntax/freshness conditions. ScopedTermProgram
interleaving is now handled with its explicit Hoistable and old-frame freshness
premises. General raw matching, general bound-output frame presentation and
final paired bisimulation/secrecy remain open. Named execution rigidity, cyclic
exclusion and the old-handle election case remain checked.

Proof notes: hoist the capture prefix before applying swapBinders, then use
restrictNames_rename and var_restrictNames to restore the exact raw target.
Base/channel inequality with free variables uses constructor discrimination,
not bare decide. Public is unfolded explicitly before concrete decidability.
All original rules and upstream revisions are unchanged.

Integrated verification: `lake build` passes **4090 jobs**; targeted controls
pass **1166 jobs**. The current log reports **4678** nonempty standard-only and
**92** axiom-free results. The claim audit covers **3784** public theorem entries
and **131** current-status documents. All five changed Lean sources have current
oleans; **1675** local links resolve. No proof holes, custom axioms, warnings or
errors were found in the checked scope; `git diff --check` passes. This increment
adds **30** theorem audits, including **22** public kernel controls, and one raw
target definition (ScopedTermProgram.capture), with no new program datatype or
operational rule.
Log: `tmp/variable-overlap/source-scoped-capture-full-build.log`.

Maintain the [blueprint](helios-proof-blueprint.md), B9/B10 item in
[task list.md](../../task%20list.md), [results](helios-results.md), and model docs.
For the public workflow, read [workflow.md](workflow.md). Local paper:
tmp/cortier-smyth-layout.txt.



### Dependent program-capture checkpoint

Latest frontier: [dependent program captures](helios-source-program-capture.md)
retains actual Scope targets for every finite existing TermProgram and normalizes
all dependent local providers into the full computed capture. Complete old-frame
and Named presentation reconstruction follow. B9/B10 remain at 8/10 milestones.

SourceLocalCaptureNormalization: swap_then_bind_local proves Scope swap followed
by local instantiation equals liftSubst(inputSubst m). scope_capture_normalize
uses original Subst/Alias to eliminate the exchanged local, retaining the whole
capture recipe and arbitrary continuation, including later input binders.
The private scope_provider lemma identifies the shifted old provider exactly.

SourceTermProgramCapture adds only TermProgram.capture, an actual raw-target
description using existing syntax. compile_output_capture derives every original
Scope without first normalizing the source. capture_normalizes handles all
retained dependent locals; capture_exports_iff identifies fresh None as the sole
export of the computation. frame_program_capture_normalize/output retain the
full old frame and capture value under outputHandle. Named
restricted_program_capture_normalize/represents and restricted_program_output
retain the original sorted prefix and give actual frame presentations and
full output targets, with only the channel-publicity premise for that action.

Twenty-one SourceProgramCaptureSPOT controls include x=old0, y=pair(x,old1),
a literal raw target with both locals and external capture, full SPK values and
all three final handles, actual Extended/Named actions and static observations.
Wrong full values are E-distinct; merging the capture into an old handle fails
structurally. A separate arbitrary continuation retains input/capture/local
coordinates and performs the same input before and after normalization.

Next: expose solvable local computations through arbitrary reachable structural
representatives. Current reconstruction covers the existing finite TermProgram
class and a general single-scope context, not all raw targets or arbitrary
interleaved ScopedTermProgram name scopes. Existing hoisting freshness premises
still apply. General raw matching, general bound-output frame presentation and
final paired bisimulation/secrecy remain open. Named execution rigidity, cyclic
exclusion and the old-handle election case remain checked.

Proof notes: qualify Extended.par/active when immediately calling .rename; the
expected type is not inferred there. Keep provider renaming folded until applying
scope_provider. Rewrite exact continuation/payload equations before unfolding
swapBinders. Use swapBinders_involutive.injective for rename. All original rules
and upstream revisions are unchanged.

Integrated verification: `lake build` passes **4087 jobs**; targeted controls
pass **1152 jobs**. The current log reports **4648** nonempty standard-only and
**92** axiom-free results. The claim audit covers **3754** public theorem entries
and **130** current-status documents. All five changed Lean sources have current
oleans; **1683** local links resolve. No proof holes, custom axioms, warnings or
errors were found in the checked scope; `git diff --check` passes. This increment
adds **31** theorem audits, including **21** public kernel controls, and one raw
target definition (TermProgram.capture), with no new program datatype or
operational rule.
Log: `tmp/variable-overlap/source-program-capture-full-build.log`.

Maintain the [blueprint](helios-proof-blueprint.md), B9/B10 item in
[task list.md](../../task%20list.md), [results](helios-results.md), and model docs.
For the public workflow, read [workflow.md](workflow.md). Local paper:
tmp/cortier-smyth-layout.txt.



### Recipe-capture checkpoint

Latest frontier: [recipe capture reconstruction](helios-source-recipe-capture.md)
proves full Structural and Named frame presentations for explicit ground-provider
frames beside fresh old-handle-recipe captures, including arbitrary plain
continuations using old/new handles. B9/B10 remain at 8/10 milestones.

SourceFrameContextSubstitution: entriesSubst_outside; substExtended_beside_context;
frameEntries_apply_extended returns an exact Instantiates graph plus a complete
Structural path, assuming the context does not export provider variables.
frameEntries_apply_instantiates uses target uniqueness. entriesSubst_shifted_frame
identifies the full shifted substitution with liftSubst of old ground values;
shiftedFrame_apply_instantiates retains fresh None and all nested local binders.
Arbitrary provider lists need not be injective for the sequential theorem;
canonical Some providers are injective for the exact per-handle evaluation.

SourceRecipeCaptureNormalization: frame_recipe_capture_ground uses the full old
frame then the fresh active provider to ground every capture/continuation use.
frame_recipe_capture_normalize renames via outputHandle into the complete
extended frame and exact evaluated body. frame_recipe_output supplies an actual
non-ground recipe output and full normalized target. Named
restricted_recipe_capture_normalize/represents retain the same sorted prefix;
restricted_recipe_output gives an actual Named bound action and full Structural
target when its channel is public. No public-recipe or secrecy claim is implied.

Eighteen SourceRecipeCaptureSPOT controls retain provider values 40/41, the full
SPK fourth field, three final handles, fresh naming, nested local/input binders,
actual static observations and Extended/Named recipe-output derivations. A
fourth-field change 42 to 43 is E-distinct and structurally impossible; old
providers cannot ground fresh None or be omitted/redefined in the context.

Next: extract the explicit provider/capture form from arbitrary reachable
structural representatives and eliminate their local definitions. This
increment constructs actual presentations for the stated syntax class, not all
raw targets. Named execution rigidity and exclusion of the cyclic joint family
remain checked; rigidity sufficiency remains unproved. General raw matching,
general bound-output frame presentation and final paired bisimulation/secrecy
remain open. The old-handle election case stays closed.

Proof notes: do not unfold shiftTerm in the same simp pass that should apply
shiftTerm_subst; first prove the shifted recipe equation explicitly. For the
continuation, groundTerm_subst handles both successive substitutions. The
identifier scoped is reserved. Named restriction fixture abbreviations need
noncomputable. All original rules and upstream revisions are unchanged.

Integrated verification: `lake build` passes **4084 jobs**; targeted controls
pass **1148 jobs**. The current log reports **4618** nonempty standard-only and
**91** axiom-free results. The claim audit covers **3723** public theorem entries
and **129** current-status documents. All five changed Lean sources have current
oleans; **1661** local links resolve. No proof holes, custom axioms, warnings or
errors were found in the checked scope; `git diff --check` passes. This increment
adds **30** theorem audits, including **18** public kernel controls, with no new
production definition or operational rule.
Log: `tmp/variable-overlap/source-recipe-capture-full-build.log`.

Maintain the [blueprint](helios-proof-blueprint.md), B9/B10 item in
[task list.md](../../task%20list.md), [results](helios-results.md), and model docs.
For the public workflow, read [workflow.md](workflow.md). Local paper:
tmp/cortier-smyth-layout.txt.



### Named execution-rigidity checkpoint

Latest frontier: [Named execution rigidity](helios-source-rigid-execution.md)
proves an all-opening local-rigidity invariant of every original Named action,
structural path and bijective public-handle change. Finite executions from any
presented/canonical state exclude the cyclic joint partner, including mapped
canonical election phases. B9/B10 remain open at 8/10 milestones.

SourceNamedLocalRigidity defines LocallyRigid with universal assignment,
actual Opens, and environment quantifiers. Opens.of_frameOf retains the exact
allocation and reconstructs the full process opening; locallyRigid_frameOf is
an equivalence. Structural.locallyRigid uses transport_binder_opening with
avoid empty, and Reduction/FreeStep use actual frame projection. BoundOutput
locallyRigid_reclose is an equivalence after hiding the new handle;
locallyRigid is forward preservation via newVar_body for every environment.
LocallyRigid.rename handles arbitrary variable equivalences, including
Extended.outputHandle; embed/newName/restrictNames provide constructors.
RepresentsFrame.locallyRigid and restrictedState_locallyRigid give base cases.

SourceRigidExecution defines Execution as finite closure of original
structural/internal/free/bound derivations and explicit bijective handle
reindexing. It is not a new action rule or the labelled matching relation.
Execution.locallyRigid/from_presented/from_canonical retain the invariant with
changing endpoint types. canonical_no_execution_to_cycle excludes the generic
cyclic family. source_coordinated_execution_rigid and
source_coordinated_no_execution_to_cycle cover any mapped canonical election
phase with explicit coordinates. No fresh/reached premise is needed for this
necessary invariant; protocol matching still needs its original premises.

Twenty SourceRigidExecutionSPOT controls retain output through variable and
sorted name scopes, next input on the new handle, a chosen private local 50
versus public capture 41, rejected capture collision, actual canonical Fin1
publication through Option and back to Fin2, private communication, semantic
joint-but-unreachable cycles and the one-way bound-output rigidity boundary.
The canonical publication control is load-bearing: without Execution.reindex,
a trace ending at a Fin type would silently omit Option-typed output targets.

Next: sufficient reachable reconstruction and matching. Necessary Named action
rigidity is now integrated, but no normalization/presentation follows solely
from it. Keep actual structural frame evidence and the semantic joint relation;
do not assume a reconstruction callback. Raw bound-output frame presentation,
arbitrary raw action matching and the final paired bisimulation/secrecy theorem
remain open. The old-handle election case remains closed.

Proof notes: Named.rename_id currently lives in SourceElectionOpeningInvariant;
import it for the inverse equivalence opening. Heterogeneous Execution endpoints
need their variable types separately specified in literal SPOT statements.
All original rules and upstream revisions are unchanged.

Integrated verification: `lake build` passes **4081 jobs**; targeted controls
pass **1397 jobs**. The current log reports **4588** nonempty standard-only and
**91** axiom-free results. The claim audit covers **3693** public theorem entries
and **128** current-status documents. All five changed Lean sources have current
oleans; **1649** local links resolve. No proof holes, custom axioms, warnings or
errors were found in the checked scope; `git diff --check` passes. This increment
adds **42** theorem audits, including **20** public kernel controls, and two
auxiliary definitions (LocallyRigid and the original-action execution closure).
Log: `tmp/variable-overlap/source-rigid-execution-full-build.log`.

Maintain the [blueprint](helios-proof-blueprint.md), B9/B10 item in
[task list.md](../../task%20list.md), [results](helios-results.md), and model docs.
For the public workflow, read [workflow.md](workflow.md). Local paper:
tmp/cortier-smyth-layout.txt.



### Binder-rigidity checkpoint

Latest frontier: [binder rigidity](helios-source-binder-rigidity.md) supplies
actual structural name-opening witnesses and extends the cyclic boundary to
full Named.Structural and every ground frame presentation. Extended bound
outputs preserve local rigidity and exactly preserve it under frame reclosure.
JointOpening alone cannot imply Named.StaticEq: its cyclic complete-frame
partner has no ground presentation under any policy/values. This is not a
reachable-election or secrecy counterexample. B9/B10 stay at 8/10 milestones.

SourceRigidityEnvironment: satisfies_env_congr, rigid_env_congr and
rigid_newVar_body. SourceRigidityBinders.rigid_varComm uses E-equivalent
environment transport to swap dependent restricted values correctly.
SourceBinderStructure defines BinderStructural with original Extended paths,
congruence and existing Named variable commutation. Its named theorem derives
an actual Named.Structural path; sameRealizations/satisfies/rigid are proved.
It adds no action or Extended structural rule.

OpeningTransport/OpeningEquivalent are strengthened IN PLACE to return
BinderStructural instead of SameRealizations. Existing parallel/variable
comparison proofs now construct binderStructural witnesses; the full name/alpha
rule induction remains shared. Structural.transport_binder_opening returns the
strong witness, and the previous transport_opening signature remains semantic
via .sameRealizations. Clients and older controls are rebuilt.

SourceBoundRigidity: BoundOutput.binder_frame_reclose relates newVar b.frameOf
to a.frameOf using BinderStructural. rigid_reclose retains exact uniqueness;
rigid_target/rigid_all_targets preserve remaining locals for arbitrary values.
The converse fails when the exported binder was itself unconstrained.

SourceNamedRigidityBoundary: Structural.binder_of_embeds, the exact
structural_embeds_iff_binder criterion, rigid_embeds and full Named separation
of the cyclic family. SourcePresentationRigidity: Opens.frameOf preserves its
allocation, Opens.canonicalFrame_rigid holds at arbitrary assignments, and
RepresentsFrame.opening_rigid forces all openings/environments rigid.
frame_with_unconstrained_local_no_presentation quantifies all target ground
frames/policies/hidden sets; no_staticEq excludes any static partner.

SourceBoundRigiditySPOT: seventeen controls, including dependent binder values,
real scoped bound output, all-target rigidity, wrong slot exchange, an actual
unconstrained export refuting converse preservation, full Named cyclic
separation, JointOpening without StaticEq and live canonical static observations.
Earlier opening-comparison controls now exercise the stronger definition.

Next: a sufficient reachable reconstruction invariant. Rigidity alone is not
proved sufficient. Use actual structural opening/frame evidence; do not assert
that JointOpening, WellFormed or semantic nonvacuity supplies a presentation.
Full Named action-invariant integration, arbitrary raw matching and raw bound
output frame presentation remain open, then final paired bisimulation/secrecy.
The existing-handle election case remains closed by publication separation.

Proof notes: declare BinderStructural before namespace variable V to avoid an
accidental unused inductive parameter. Structural induction changes the type
index in varComm; type local helpers with the case's index. Opens.frameOf's
embed case needs Named.frameOf unfolded alongside Extended.frameOf_mapNames.
The source model's existential Named.Models cannot naively define rigidity by
ignoring name choices: nameVarComm would move those quantifiers. Strong actual
openings avoid that shortcut; no such Named rigidity definition was introduced.

Integrated verification: `lake build` passes **4078 jobs**; the targeted controls
pass **1370 jobs**. The current log reports **4546** nonempty standard-only and
**91** axiom-free results. The claim audit covers **3651** public theorem entries
and **127** current-status documents. All fourteen changed Lean sources have
current oleans; **1627** local links resolve. No proof holes, custom axioms,
warnings or errors were found in the checked scope; `git diff --check` passes.
This increment adds **42** theorem audits, including **17** public kernel
controls, and one auxiliary comparison definition. Existing opening comparisons
are strengthened in place; the previous semantic transport interface and its
avoidance control remain checked.
Log: `tmp/variable-overlap/source-binder-rigidity-full-build.log`.

Maintain the [proof blueprint](helios-proof-blueprint.md), B9/B10 item in
[task list.md](../../task%20list.md) and [results ledger](helios-results.md).
For the public workflow, read [workflow.md](workflow.md).
Local Figures 2–4 and Definition 1: tmp/cortier-smyth-layout.txt.



### Extended-rigidity checkpoint

Latest frontier: [local-solution rigidity](helios-source-local-rigidity.md)
refutes the proposed Extended normalization shortcut. WellFormed plus a
nonempty full realization class does not imply Extended.Structural canonical
presentation, even beside any complete frame and body. The final secrecy goal
is unchanged and unproved; B9/B10 remain at 8/10 unweighted milestones.

SourceLocalRigidity defines Extended.Rigid a env. Plain/active are rigid;
parallel requires both component rigidities when both constraints hold;
newVar requires uniqueness modulo E of satisfying local values and body
rigidity under each satisfying extension. Unsatisfiable systems are vacuously
rigid, so existence remains separate. rigid_rename/rigid_frameOf/rigid_newPar
and Structural.rigid are proved for every original Extended structural rule.

SourceRigidityPreservation proves internal/free preservation via frameOf,
frameEntries_rigid/activeFrame_rigid/frameProcess_rigid and the necessary
Structural.rigid_of_frame_target criterion for Extended normalization.
Bound-output rigidity and the full Named calculus are not yet covered.

SourceRigidityBoundary proves νx.{x/x} has nil's complete class but is not rigid:
names 40 and 41 are E-distinct solutions. Adding this local beside any complete
canonical frame/process preserves WellFormed and full SameRealizations, yet
cannot normalize to that canonical partner by Extended.Structural. It also
has an embedded Named.JointOpening partner. The Named.Structural separation
is NOT proved; do not infer it from the Extended theorem.

SourceLocalRigiditySPOT has thirteen public controls. An independent ground
alias normalizes; the cycle is well formed/nonempty but non-rigid. The universal
WellFormed/nonempty-class-to-Structural conjecture is explicitly refuted. A
conditional step retains nontrivial ground-alias rigidity. A complete public
frame/input body with the cycle still performs an actual public input, so
this is not an action-matching or immediate-stuckness counterexample.

Next: prove an adequate reachable reconstruction invariant. Rigidity is a
necessary condition for Extended presentation; sufficiency is NOT proved.
Lift it through Named fresh openings/additional binder rules and bound output
if using it in the final relation. Do not assume JointOpening, nonvacuity or
WellFormed supplies a Structural or raw StaticEq witness. Avoid reattempting
the refuted Extended implication without a new load-bearing hypothesis.
Arbitrary raw matching-action construction and raw bound-output frame
presentation remain open, then paired weak labelled bisimulation and secrecy.
[Publication separation](helios-source-publication-separation.md) still closes
the existing-handle election case with its fresh/reachable hypotheses.

Proof notes: Structural induction hypotheses quantify the environment, so
symm/trans use ih env. Scope extrusion's rigidity proof gates on all component
constraints. The bound-output frame reclosure theorem is Named.Structural,
even for Extended.BoundOutput, because it uses variable-binder commutation;
it cannot directly feed Extended.Structural.rigid.

Integrated verification: `lake build` passes **4071 jobs**. The current log
reports **4504** nonempty standard-only and **91** axiom-free results. The claim
audit covers **3609** public theorem entries and **126** current-status documents.
All six changed Lean sources have current oleans; **1624** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **30** theorem audits,
including **13** public kernel controls, and one auxiliary proof definition.
The targeted control build passes **1210 jobs**.
Build log: `tmp/variable-overlap/source-local-rigidity-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-local-rigidity-verification.txt`.

Maintain the [proof blueprint](helios-proof-blueprint.md), B9/B10 item in
[task list.md](../../task%20list.md) and [results ledger](helios-results.md).
For the public workflow, read [workflow.md](workflow.md).
Local Figures 2–4 and Definition 1: tmp/cortier-smyth-layout.txt.

### Publication-separation checkpoint

Latest frontier: [publication separation](helios-source-publication-separation.md)
closes the election-level existing-handle output case. Every actual publication
in a reached fresh election differs modulo full E from every old handle.
Arbitrary jointly related raw representatives therefore cannot perform any
existing-handle free output, in any current name coordinates. Original source
rules remain unchanged. B9/B10 stay at 8/10 unweighted milestones; secrecy is
unproved.

SourcePublicationSeparation: fresh_ballots_distinct uses first ciphertext/nonce
injectivity. candidateTuple_not_ballot uses full-E tuple length; candidate tuples
have n+1 cells and ballots 2(n+1)+1. candidateTuple_not_initial_handle covers
key and both ballots. source_results_not_partials uses a numeric first result
versus a partial-decryption constructor. Publication.old_handle_distinct
handles every old index in all four publications and discharges numeric results
from reached public/accepted history via hr.swap hf false. Full source values
are retained via sourcePartials_eqE/sourceResults_eqE.

SourceElectionHandleExclusion: source_coordinated_no_handle_output reflects an
assumed raw old-handle output, retains full old-value equality under inverse
coordinates, obtains its actual Publication and contradicts old_handle_distinct.
It quantifies all channels/targets and does not need channel freshness.
source_joint_no_handle_output specializes to identity coordinates.
CoordinatedPhaseOpening.no_handle_output transports the raw domain equality.
This is exclusion of the old-handle case, not a fresh output with a dropped or
reused domain. Generic handle-output closure remains separately checked.

SourceElectionHandleSPOT: thirteen controls, including all four value
separations and all four actual live bound outputs in both vote worlds with
nonidentity name coordinates, all-target result output exclusion, noncanonical
parallel second-ballot exclusion and nonce-collision controls. Equal nonces and
votes make whole ballots identical; the fixture is proved non-fresh. A real
colliding-value Out-Atom prefix remains allowed by the unchanged rules.

Next: arbitrary raw matching-action construction and raw bound-output frame
Structural presentation. The current joint relation carries a nonempty full
semantic class but is not itself a Structural or StaticEq presentation. Inspect
normalization/reachability evidence rather than inserting a reconstruction
callback. Then build the final paired same-coordinate relation, discharge all
weak labelled bisimulation clauses and prove symbolic secrecy. Existing-handle
free-output classification is now closed by the general exclusion above.

Proof engineering: give nonce injectivity's product endpoints explicit types.
For the result frame's old indices, unfold sourceView/sourcePartialFrame and
use Frame.extend_old. After cases on raw-domain equality, the surviving index
is phase.handles. Give restricted_handle_output_derivable an explicit frame
when elaboration cannot infer it through the restrictedState wrapper.

Integrated verification: `lake build` passes **4067 jobs**. The current log
reports **4474** nonempty standard-only and **91** axiom-free results. The claim
audit covers **3579** public theorem entries and **125** current-status documents.
All five changed Lean sources have current oleans; **1620** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **21** theorem audits,
including **13** public kernel controls, and no production definitions.
The targeted control build passes **1437 jobs**.
Build log: `tmp/variable-overlap/source-election-handle-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-election-handle-verification.txt`.

Maintain the [proof blueprint](helios-proof-blueprint.md), B9/B10 item in
[task list.md](../../task%20list.md) and [results ledger](helios-results.md).
For the public workflow, read [workflow.md](workflow.md).
Local Figures 2–4 and Definition 1: tmp/cortier-smyth-layout.txt.

### Generic existing-handle checkpoint

Latest frontier: [existing-handle outputs](helios-source-handle-output.md).
Generic free-output target-class and joint-opening closure are checked with
all old frame values/domain, actual restrictions and exact public channel.
Canonical old-handle output is derived from Subst/Out-Atom/Scope. The earlier
[coordinated-phase results](helios-source-coordinated-phases.md) remain checked.
B9/B10 stay incomplete at 8/10 unweighted milestones (80%); secrecy is unproved.

SourceHandleOutputClosure: FreeStep.output_sameRealizations_target needs an
actual action, complete source class and continuation determinism restricted
to outputs E-equal to φ.value x. It proves full target-class equivalence in all
environments. output_of_sameRealizations retains the full emitted value.
SourceJointHandleOutput: handle_output_step/target/handle_output retain the
literal channel, full handle equality, old domain and joint target. The paired
fresh endpoint proof fixes the channel and maps full handle values both ways.
SourceHandleOutputDerivation: frame_handle_output_derivable and
restricted_handle_output_derivable construct actual actions for canonical
prefixes outputting exactly φ.value x. Public-channel scope is explicit.

SourceHandleOutputSPOT: twelve controls cover actual full SPK output, full
noncanonical target class, joint closure, wrong labelled handle, changed emitted
and unemitted values, an E-equivalent projection value, parallel padding and
private-channel blocking. Two SPKs differ only in their fourth-field names.
No new production definitions or source rules were introduced.

Next: arbitrary raw action construction and raw bound-output frame Structural
presentation still require a stronger proved normalization/reachability bridge.
WellFormed supplies unique definitions/scope only; no cyclic counterexample or
normalization implication was proved by inspection. JointOpening is not a
Structural presentation or a raw StaticEq witness.
Also integrate existing-handle free outputs at election level. Generic closure
is now solved, but such outputs retain the old domain: the current phase
publication wrapper adds a fresh handle. Prove exclusion in election states or
supply a corresponding old-domain relation; do not assume these actions absent.
Then complete paired same-coordinate weak labelled bisimulation and secrecy.
No construction from an arbitrary related raw counterpart is proved merely by
constructing an action from its canonical partner.

Integrated verification: `lake build` passes **4064 jobs**. The current log
reports **4453** nonempty standard-only and **91** axiom-free results. The claim
audit covers **3558** public theorem entries and **124** current-status documents.
All six changed Lean sources have current oleans; **1601** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **19** theorem audits,
including **12** public kernel controls, and no production definitions.
The targeted control build passes **1420 jobs**.
Build log: `tmp/variable-overlap/source-handle-output-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-handle-output-verification.txt`.

Maintain the [proof blueprint](helios-proof-blueprint.md), B9/B10 item in
[task list.md](../../task%20list.md) and [results ledger](helios-results.md).
For the public workflow, read [workflow.md](workflow.md).
Local Figures 2–4 and Definition 1: tmp/cortier-smyth-layout.txt.

### Coordinated-phase checkpoint

Latest frontier: [coordinated phases](helios-source-coordinated-phases.md) retain
shared canonical name coordinates through arbitrary input freshening, actual
check-phase matching, subsequent raw internal traces and bound outputs.
A same-label input is constructed from the other fresh canonical partner.
Matching-action construction in arbitrary related raw counterparts and raw
output-frame presentation remain open. B9/B10 stay incomplete at 8/10
unweighted milestones (80%); symbolic secrecy is unproved.

SourceMappedCanonicalStates defines Named.mappedState hidden s e k as
restrictedState(hidden.image k)(s.mapNames e k). Identity recovers restrictedState;
composition is actual Named equality:
mappedState(hidden.image k)(s.mapNames e k) f l =
mappedState hidden s(e.trans f)(k.trans l).
This does not assert that arbitrary global renaming is Structural. It avoids
dependent policy casts while retaining both policies and the full frame/body.
Agent.Visible.input_inverse_frame/forward_frame retain the complete recipe
under inverse coordinates and return the exact literal mapped label.

SourceCoordinatedPhases defines CoordinatedPhaseOpening ns swap left right extra
ch e k phase a := ∃hh:rawHandles=phase.handles, JointOpening(a.rename(Fin.cast hh))
(mappedState ch.privateChannels(sourceState ... phase)e k). Coordinates are
explicit, so both worlds can share them. canonical/of_joint/structural/identity
and channels are proved. There is no separate existential coordinate hidden
independently in each vote world.

SourceCoordinatedInput.source_coordinated_public_input_next takes an actual
raw input and r.Public(ns.restricted.image e), derives original Public for
r.mapNames e.symm, reflects the input to original source coordinates, and
identifies rs,s:Recipe3 with phase=input rs, HEq(r.mapNames e.symm)s,
c=k(ch.voter(rs.length+2)), actual stage input Step to check rs s, and full
CoordinatedPhaseOpening of the unchanged raw target. Full target determinism
is discharged for actual residuals. Acceptance is not an input premise.

SourceCoordinatedFreshInput.source_coordinated_common_input_next takes both raw
joint relations to mapped canonical states with the SAME e,k, ns.Fresh,
ch.Fresh and a reached phase. No Public premise is needed on the raw recipe.
It freshens both mapped canonical partners together, composes e.trans f/k.trans l,
then invokes the public-input classification. It returns phase/recipe/channel
identities, actual input Step and reached check phase, full raw target relation,
both raw source relations under the new coordinates, full old-frame StaticEq,
and a real matching Named input from the other NEW CANONICAL partner with the
same literal raw label. That canonical target has the same coordinated check
phase. It does not construct the input from the arbitrary raw partner d.

SourceCoordinatedInternal.source_coordinated_internal_next reflects mapped Tau,
uses residual completeness/determinism and casts the full target with
JointOpening.cast_mapped_state. CoordinatedPhaseOpening.internal and
.internal_trace retain current coordinates through actual raw internal steps
and every finite trace from a reached phase. .bound_channel_public uses the
mapped private-channel set. SourceCoordinatedOutput.source_coordinated_output_next
reflects full output values to a Publication, reports c=k ch.broadcast, and
retains the complete output target at the next phase/current coordinates.
Publication.next_handles/target_state supply exact new domain and full state.

SourceCoordinatedSPOT has 20 controls. e swaps secretKey/100; k swaps trustee/200;
f and l move those fresh values again. Reversed composition is rejected.
The old secret literal is private originally but public now, inverse recipe
name100 is public, and an actual election input reaches check. Both-world
common refresh/matching is exercised from nonidentity current coordinates.
A real internal accept-or-reject step follows; all finite raw internal traces
from that reached check retain coordinates. Private trustee output is blocked.
First publication retains coordinates and the new domain. No claim that the
literal input is accepted is made. Full fourth-field observation support stays.

Next: close the source-action converse for arbitrary related raw processes and
raw output-frame Structural presentation. The current common-input theorem
constructs actions only from the canonical counterpart; merely replacing it
with related raw d would assume the missing obligation. Inspect current source
WellFormed/UniqueDefinitions/admissibility and normalization interfaces to find
an adequate reachable invariant; use controls to test cyclic or unused active
constraints. JointOpening includes a nonempty full realization class but does
not imply Structural presentation, transitivity or Named.StaticEq by itself.
Existing-handle free-output target-class closure also remains open and must be
included in the final source relation. Then assemble the paired same-coordinate
relation with reachability/static observations and prove all weak labelled
bisimulation clauses and final symbolic secrecy. Do not mark B9 complete from
one-direction stage consumption alone.

Proof-engineering notes: when mapping sourceState, explicitly unfold sourceState
in simp to expose frame/body projections. For the common-input label, use a
local mapped ScopedStep, change its label to input(k' voter)(s.mapNames e'), then
rw the exact channel/recipe identities; a single simp did not rewrite the
recipe in that dependent label. For concrete Public/inRange checks, change to
literal membership/arithmetic before decide. No operational rule was weakened.
Keep full E/E0, structured-key E5, full-ciphertext E6, all SPK fields and public
observations. Base-name syntax support is not generally E-invariant.

Integrated verification: `lake build` passes **4060 jobs**. The log reports
**4434** nonempty standard-only and **91** axiom-free results. The claim audit
covers **3539** public theorem entries and **123** current-status documents.
All nine changed Lean sources have current oleans; **1578** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **37** theorem audits,
including **20** public kernel controls, and two proof definitions.
The targeted control build passes **1431 jobs**.
Build log: `tmp/variable-overlap/source-coordinated-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-coordinated-verification.txt`.

Maintain the [proof blueprint](helios-proof-blueprint.md), B9/B10 item in
[task list.md](../../task%20list.md) and [results ledger](helios-results.md).
For the public workflow, read [workflow.md](workflow.md).
Local Figures 2–4 and Definition 1: tmp/cortier-smyth-layout.txt.

The following paragraphs retain the development history. Their lists of open
frame cases are superseded by B8's completed theorem above.

[Published-frame name protection](helios-published-protection.md) now covers all
nested public recipes in the partial frame and, for public submissions, the
final frame. It also excludes restricted composition factors and constructed
election keys/trustee partials. No acceptance or freshness premise is needed
for these name-secrecy results. Extended value origins and two-world equality
observations remain the next B8 work.
The [individual-handle frame](helios-expanded-published-frames.md) now gives an
exactly equivalent proof presentation. Its published values have one-node
minimum representatives; published trustee-partial minima are partial-slot
handles, and a bound tally decryption is shortened by its result handle.
Use the exact static-equivalence criterion to return to the protocol's tuple
frames. Minimum costs themselves do not transfer between presentations.
[Expanded value origins](helios-expanded-value-origins.md) now prove minimum
pair/ciphertext origins, no successful E5/E6 match of a whole minimum
decryption, and the complete constructed-or-borrowed partial-value form.
Accepted elections discharge the numeric-result premise. The partial equality
branch is checked under smaller observations, and minimum children give a
minimum constructed partial. Remaining value branches and the global expanded
observation/shared-minimum induction are the current B8 work.
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

Sequential acceptance, shared numeric tallies, initial-frame equivalence and
published-frame equivalence are complete. Eight of ten milestones are complete;
B9/B10 remain open. Latest integrated evidence is recorded below.

The main library is `ExplainableCrypto`, now pinned to Lean and Mathlib 4.33.1
with VCVio for `ExplainableCrypto.Helios.Computational`. Run `lake build` at
the root for both symbolic and computational code. Reference checkout pins
and their native validation toolchains remain unchanged.
Confluence modulo E0 is machine-checked for the encoded symbolic theory, with
no remaining local-confluence assumption. Full E equality is equivalent to
joinability; irreducible E-equal terms are E0-equal. Constructor injectivity,
separation, destructor paths and arithmetic output restrictions are checked.

The initial three-handle historical frames cover both swapped assignments and
every positive candidate count. Individual and composed restricted nonces are
non-deducible under explicit protection/public-recipe premises. Honest proof
validity and corrected acceptance are checked on an empty board and after the
other fresh honest voter. The nonce-only policy remains separate from the full
frame restriction, which also forbids the key and auxiliary names.

The minimum-recipe structure milestone is now complete. The simultaneous
historical induction classifies pair origins and derives ciphertext-product
certificates for every minimum public ciphertext recipe under the supplied key.
It returns a strictly smaller public plaintext with exact nonce/message E-values.
Raw ciphertext forms contain explicit penc constructors, honest ciphertext
selectors and multiplication. Minimum proof forms contain explicit spks or
honest component/aggregate proof selectors.

Every minimum historical decrypt retains normal-form composition without a
caller-supplied ciphertext certificate. Minimum projections either have a
bounded honest tuple tail as their argument or compose normal values modulo E0.
The exception retains indexed fst/snd chains. These results preserve the actual
initial frame, public-name policy and normal-representative hypotheses; they do
not claim that substituted minimum recipes are already irreducible.

Accepted-ballot constructor reconstruction (source Lemma 9 with the authorised
tail-guard correction) is machine-checked for all valid ground candidate
substitutions, every positive count and both swaps. `Historical.General.frame`
is the full candidate model; the selected-index `Historical.frame` remains a
specialization. Honest abstention and reducible E-equivalent bit representations
are covered. Raw general frames need not satisfy syntactic nonce protection:
each public recipe has an E-equal protected value via a literal-bit frame.

`Historical.General.accepted_ballot_constructor_recipe` excludes borrowed
component and aggregate proofs and constructs nonce-public ciphertexts with
literal bits satisfying the candidate sum before substitution. Acceptance and
both honest board members are explicit premises. The witness may depend on the
supplied world. See the [candidate-substitution record](helios-candidate-substitutions.md).

The next open task is static equivalence of the honest ballot frames and final
frames containing public partial decryptions (Lemmas 10–12). Use the general
candidate frame and its full name restriction. Congruence between representations
of the same vote is not a proof that swapping votes preserves observations.
Historical process matching and ballot secrecy also remain open.

The [static-equivalence transfer interfaces](helios-static-equivalence.md) are
checked: reconstruction preserves any caller policy containing the honest
nonces, including the full restriction. Assuming actual frame static equivalence,
one shared constructor witness and literal bit vector work in both worlds.
Acceptance transfers over the same public board recipes. The all-recipe swap
obligation reduces to valid literal bit vectors and remains open. Preserve the
nonce-collision, key-policy and raw-observer-incompleteness controls.

The [enriched-ciphertext analysis](helios-enriched-ciphertexts.md) refutes the
encoded E0 reflection step of source Lemma 10 Claim 2: adding a public zero can
be invisible after a bit substitution while remaining distinct before it.
Both public recipes are equal in both worlds; this is not a privacy attack.
Use the checked numeric-offset equality rule, which preserves atom multiplicity
and numeric value after a numeric contribution is present. Full-E equality of
arbitrary nonempty honest ciphertext products is now exactly nonce-index bag
equality under freshness. Fixed-payload equality after a common honest sum is
also invariant even when that sum changes. The
[mixed-ciphertext reduction](helios-mixed-ciphertexts.md) handles a public
encryption multiplied by a nonempty honest combination: equality is exactly
honest-bag agreement plus public nonce and zero-padded payload equality. The
last two observations are strictly smaller than the mixed recipes. Protected
E-values suffice; raw substituted safety is not assumed. Transfer of those
smaller observations, arbitrary public recipe closure and final partial
decryptions remain open. The subsequent
[ciphertext grouping](helios-ciphertext-grouping.md) connects arbitrary
constructed/honest products to those cases. Every minimum ciphertext recipe
has an exact assembly; full-E inversion derives common-key agreement at each
leaf. Grouping preserves publicness and target components, with smaller nonce,
payload and key observations bounded against the original recipe. It keeps
public-only and honest-only cases separate, without inserting unit terms.
The [ciphertext observation induction](helios-ciphertext-observations.md) now
classifies all nine grouped comparisons and transfers recursive key coherence
from smaller public equality tests. `minimum_ciphertext_equality_swap` closes
the ciphertext-valued minimum-recipe branch under that induction hypothesis,
without assuming second-world coherence or preserved minimum syntax. The
smaller-observation hypothesis remains unproved globally. The
[proof-valued branch](helios-proof-observations.md) now transfers under the same
hypothesis: honest proof comparisons follow nonce provenance, while constructed
proofs retain all four argument tests. Preserve the one-candidate exception,
where a voter's component and aggregate proof fields coincide. The
[public-key-valued branch](helios-public-key-observations.md) now derives exact
constructed/election-handle forms from minimum size and transfers their equality
tests under the full secret-name restriction. Actual projection and decryption
paths are classified first; nonminimum wrappers and nonce-only-policy controls
remain explicit. The
[initial-frame partial-decryption branch](helios-partial-decryption-observations.md)
now derives explicit constructor syntax from minimum size and transfers both
ordered component tests under the same bounded premise. A checked one-handle
frame publishing a partial decryption refutes extending that origin claim
beyond the initial frame. The [pair-valued branch](helios-pair-observations.md)
now derives constructed/nonempty-tail forms and handles all their comparisons.
Suffix length and the final aggregate proof identify fresh tails; constructed
pairs use smaller tests against both projections of the other recipe. The
[atomic branch](helios-atomic-observations.md) now forces atomic minima to be
literal names/constants and preserves their exact evaluation in any destination
frame, without freshness or a smaller-test premise. The
[destructor observation results](helios-destructor-observations.md) now classify
successful minimum projections as honest fields/nonempty tails and derive
checkspk origins for minimum stuck-check values. Their equality transfers from
smaller whole-check/ok probes and three argument comparisons; no destination
failure premise is assumed. The [stuck-destructor results](helios-stuck-destructors.md)
now derive exact minimum fst/snd/dec origins and full-E argument injectivity.
Source equalities transfer forward using smaller argument tests without
assuming destination stuckness. The [decryption probe results](helios-decryption-probes.md)
now preserve failure and prove two-sided equality transfer for minimum
decryptions with partial-decryption-valued first arguments and ciphertext-valued
second arguments. Three probes below the decryption's own size retain both E5
and E6 and derive destination coherence/failure. The
[value-shape results](helios-value-shapes.md) now reflect pair, ciphertext and
partial constructor values simultaneously for every source minimum recipe.
They discharge all decryption argument-shape premises and derive destination
failure for every minimum decryption and stuck projection. Both complete
stuck-destructor minimum equality branches now transfer in both directions.
The [composition branch](helios-composition-observations.md) now derives raw
compose origins and indivisible semantic factors in both worlds. Its full-E
factor bags retain multiplicities, and smaller public leaf tests transfer
composition equality in both directions. The
[addition branch](helios-addition-observations.md) now retains optional numeric
presence/count and nonnumeric atom multiplicity. Exact addition/zero/one origins
derive both worlds' semantic atom conditions, and smaller public leaf tests
transfer equality in both directions, including the numeric-collapse cases.
The [non-ciphertext multiplication branch](helios-multiplication-observations.md)
now derives normal partitions in both worlds, retaining internal ciphertext
fusions and exact original recipe bounds. Smaller public group comparisons
transfer equality and reassemble the whole recipes. The global
smaller-observation premise and transport of arbitrary nonminimum evaluations
remain open.

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

The agreed order remains historical symbolic analysis with the documented tuple
correction, followed by a concrete cryptographic repair.

## Restore the workspace

With Git, Lean's `elan` manager, Python 3 and curl available:

```sh
git clone https://github.com/fplaunchpad/explainable-cryptography.git
cd explainable-cryptography
git submodule update --init
python3 scripts/fetch_references.py
lake exe cache get
lake build
```

For an existing clone, pull `main` and run the same submodule, reference and Lake
commands. `git submodule update --init` fetches the pinned research libraries. Nested optional native backends are unnecessary for the
main build. The upstream libraries have different Lean versions and are not
Lake dependencies of `ExplainableCrypto`.

The reference downloader retrieves the three exact Helios papers recorded in
[reference-papers.json](reference-papers.json). It verifies SHA-256 before writing
and refuses to replace an existing mismatched file. All three remote downloads
were checked against these hashes during handoff. Use
`python3 scripts/fetch_references.py --check` for an offline verification.
Other local material in `_references/`, build caches, and generated files in
`tmp/` or `output/` are ignored and are not transferred by Git. They are not
needed to build the formalisation. Paper text can be re-extracted with Poppler's
`pdftotext -layout` if useful.

## Resume the research

Read [AGENTS.md](../../AGENTS.md), the [workflow](workflow.md), and the canonical
[task list](../../task%20list.md). Continue at the first open item in section 3.
The confluence results require careful interpretation:

- `triple_peak_joined` is unconditional for arbitrary terms under one common key.
- `root_peak_joined` covers all pairs of root-rule instances with E0-equivalent
  sources. E0 constructor inversion and quotient multiplication factors supply
  its proof. Later root/internal analyses and the global induction complete
  the singleton-source obligation.
- `variable_peak_joined` joins a root-rule instance and a reduction inside one
  occurrence of a substituted variable, including repeated parameters in
  decryption and proof checks. Its explicit schema context does not establish
  coverage of fixed-constructor overlaps or arbitrary E0 representatives.
- `baseEq_iff_mulFactors` proves completeness of the quotient factor
  representation. `homomorphic_selection_reachable` exposes any specified pair;
  the shared/disjoint selection lemmas retain exact branch bags.
- `pair_selection_cases` classifies arbitrary two-element selected bags with
  multiplicity. `outer_fusion_peak_joined` joins every pair of `OuterFusion`
  witnesses, discharging the generic bag-rule laws for E7.
- `ModuloStep.penc_cases` classifies ciphertext steps by the changed component.
  `fusion_factor_peak_joined` handles both selected and disjoint factor steps,
  including key synchronization and factor expansion.
- `ModuloStep.factor_cases` covers all modulo steps as outer fusion or
  single-factor reduction. `outer_fusion_modulo_peak_joined` therefore joins
  any peak with at least one outer fusion.
- `disjoint_factor_reductions_joined` handles expanding outputs and arbitrary
  remainders. `local_confluence_iff_single_factor` reduces full local confluence
  to `SingleFactorLocalConfluent V`, now proved by
  `single_factor_local_confluence`.
  `locally_confluent_at_penc` retains explicit component hypotheses.
- `ModuloStep.unary_cases` and `ModuloStep.rigid_binary_cases` classify root and
  argument reductions. `unary_root_inner_joined` closes the projection mixed
  cases. Unary, pairing and partial-decryption local confluence follows from
  explicit argument hypotheses; atoms are irreducible.
- `RootModuloStep.decryption_cases` exhausts E5/E6 roots. The two
  `decryption_root_*_joined` theorems synchronize arbitrary internal changes,
  including repeated keys and ciphertexts. `locally_confluent_at_decryption`
  retains only its two argument hypotheses.
- `locally_confluent_at_spk` and `locally_confluent_at_checkspk` complete the
  non-AC constructor implications. E8/E9 root/internal synchronization is
  unconditional. `proof_check_step_reaches_ok` and
  `locally_confluent_at_matching_check` need an actual checking-root witness,
  rather than component hypotheses.
- `baseEq_iff_composeFactors` reconstructs nonce-composition classes, and
  `ModuloStep.compose_factor` covers every composition-context step. Disjoint
  replacements join; `locally_confluent_at_of_compose_factors` retains the
  selected-factor local-confluence premise.
- `baseEq_iff_addSummary` characterizes E0 addition with exact atom multiplicity
  and optional numeric counts. `Term.add_subsummary_representable` reconstructs
  nonempty remainders with valid atoms. `ModuloStep.add_factor` classifies all
  addition steps; disjoint replacements join.
  `locally_confluent_at_of_add_summaries` retains the factor-local premise, and
  `irreducible_of_add_atoms_empty` covers numeric-only summaries.
  The global simultaneous induction now supplies all component/factor premises.
  Do not assume strict crypto-weight descent from a product to a factor.
- `ordinary_rewriting_confluent` covers all ordinary contextual reductions.
  `raw_normalization_incomplete_modulo` retains an E0-only decryption match,
  so raw normalization is not a replacement for modulo confluence.
- `local_confluence_modulo` and `confluence_modulo` are unconditional.
  `eqE_iff_join`, `irreducible_eqE_iff_base` and `normal_forms_unique_modulo`
  expose the equality consequences.
- `EqE.penc_iff`, `EqE.spk_iff`, `EqE.pair_iff` and
  `EqE.partialDecrypt_iff` now give full-E ordered component equality for arbitrary
  inputs. The [full-E structure record](helios-full-structure.md) documents
  constructor separation and normal-form shape restrictions.
  `EqE.pk_iff` supplies public-key injectivity;
  `ReducesModulo.projection_cases` and `EqE.projection_penc_inversion` supply
  actual pair-producing paths without assuming initial literal pair shape.
- `Frame.nonce_not_deducible` quantifies over every public recipe and retains
  explicit per-handle protection. See the [nonce record](helios-nonce-nondeducibility.md).
  `Frame.composed_nonce_not_deducible` also excludes any composition target with
  a restricted-name factor; target irreducibility is unnecessary. The initial
  frame instantiation follows below; final-frame analysis remains separate.
- The [initial historical frames](helios-historical-frames.md) instantiate
  protection and non-deducibility for all positive counts and both worlds.
  The nonce-only restriction matches Lemma 9; the full restriction additionally
  excludes secret-key deduction. Honest validity and scoped acceptance retain
  freshness, replay and collision controls.
- [Minimum public recipes](helios-minimal-recipes.md) retain the substitution,
  handle type and name policy. Existence is logical, not an executable minimizer.
  Minimum subterms and ordinary irreducibility support semantic E5–E7 cancellation.
  The minimum handle with a reducible value and the raw-normal nonminimum controls
  remain necessary boundaries.
- Full-E multiplication inversion supplies both operand ciphertext values under
  the output key and exact combined nonce/message equations, including expanding
  factors and E0-only key matches. Arithmetic sources and proof checking have
  their checked output-head restrictions. Full-E checking success retains its
  bit, common nonce and complete ciphertext-binding constraints.
- `TupleProjectionChains.lean` and `HistoricalProjectionChains.lean` classify all
  fst/snd chains: pair values are bounded tails; ciphertext values select honest
  ciphertext fields; ballot proof values select component/aggregate fields.
  The public-key handle cannot supply ciphertexts or proofs by a selector chain.
  The first out-of-range field remains fst(bottom), preserving the guard control.
- `HistoricalMinimumOrigins.lean` proves the simultaneous minimum pair/ciphertext
  induction. The certificate is now derived for every minimum ciphertext recipe
  over the actual frame, with arbitrary name policies and semantic target keys.
  The smaller plaintext is public and has the exact target value. The result does
  not generalize to an arbitrary frame publishing a one-node ciphertext.
- `HistoricalCiphertextForms.lean` and `HistoricalMinimumProofs.lean` refine raw
  syntax to explicit constructors, actual honest selector positions, and (for
  ciphertexts) products. These are necessary origin forms under supplied E-values;
  the component-proof weeding step is now checked separately. See the [origin ledger](helios-minimal-recipes.md#minimum-historical-origins-and-destructor-composition).
- `HistoricalMinimumDestructors.lean` discharges the general decryption case and
  the binary-selector version of source (*). No right-argument certificate or
  initial literal ciphertext shape is assumed. Representative normality remains
  explicit. The projection exception gives the exact bounded honest tail argument,
  so an outer fst is an indexed field selector and an outer snd advances a tail.
  Three-node minimum decryption, two-node minimum stuck projection and minimum
  second-field controls instantiate both retained-head and exception cases.
- `BallotValues.lean` proves the exact semantic validity equivalence and the
  component proof-binding exclusion. `BallotTupleValues.lean` reconstructs the
  checked finite tuple with the corrected guard. `HistoricalAcceptedProofs.lean`
  applies weeding to minimum proof forms, with both honest ballots explicitly
  present on the board. `HistoricalAggregateExclusion.lean` now excludes the
  aggregate branch for nonce-public ballots, using nonce-fold counts or the
  single-candidate weeding case. `AcceptedBallotReconstruction.lean` constructs
  the public ciphertext tuple directly from minimum proof nonce arguments.
  `GeneralCandidateFrames.lean`, `GeneralMinimumOrigins.lean`,
  `GeneralMinimumProofs.lean`, `GeneralAcceptedProofs.lean`,
  `GeneralAggregateExclusion.lean` and `GeneralAcceptedReconstruction.lean`
  carry these arguments to every valid ground candidate substitution.
  `GeneralCandidateProtection.lean` uses E-equal protected values, avoiding a
  false raw-protection premise for reducible candidate representatives.
- `rootReduce` is complete for raw root rules. Its failed-match result does not
  establish irreducibility modulo E0 or under contexts.
- [The tuple-termination correction](helios-symbolic-tuple-guard.md) is authorised
  and implemented. Keep its literal-source counterexample in the audit.

See the [confluence record](helios-confluence.md) for the current declarations,
test scope and remaining overlap analysis. Do not start the computational-library
phase by treating the conditional symbolic results as a completed privacy proof.

## Validation at handoff

`lake build` passes (3525 jobs), including the finite attack, rewriting,
three-ciphertext, variable-overlap, constructor-structure, factor and raw
normalization campaigns, factor-reconstruction and selection controls, and the
exhaustive pair-selection and ciphertext-component gates, and mixed-fusion
controls for key synchronization, E0 target changes and factor expansion, plus
the singleton-selection and projection-member gates and their endpoint controls.
The unary controls include nontrivial locally confluent projection and
partial-decryption sources, plus E0 representative and ordered-pair fixtures.
The decryption gate and controls cover E5/E6 parameter synchronization, all
seven E6 change locations and fixed updated-plaintext endpoints. The checking
gate and controls cover both bits, all four key and three nonce occurrences,
expanded E0 vote fields and binding/bit rejection. The composition gate and
controls retain expanding factors, E0 representatives, empty remainders and the
unchanged exported multiplication operation. Addition controls retain numeric
presence, repeated ones and atoms, mixed-summand reconstruction and nested E0
representatives; its three seeded campaigns and 256-input backstop pass.
Addition replacement controls include two numeric-output projections, both
routes to an exact one+name endpoint, output expansion and a locally confluent
source. Its replacement gate passes the same seeds and backstop; the false
numeric-cancellation control is retained as a checked counterexample. The
global induction mechanics gate passes all three seeds and 256 inputs; its
controls retain a mixed-AC peak, an E0-only decryption, exact common endpoints
and full-E distinctions between names and zero/one. The passive-constructor
gate and controls cover reducible inputs, changed plaintext/binding fields,
argument order and the irreducible-target shape restriction. Public-key and
projection controls cover nested pair revelation, both selected outputs and
stuck names; the three-seed gate and 256-input backstop pass. The protection
gate and controls cover public ballot projection, known-key bit decryption,
unsafe-frame/literal-name leakage and the limits of plaintext protection and
reverse-E preservation. Composed-nonce controls retain repeated factors, a
reducible target with an expanding remainder, and derivability of ciphertexts
with protected randomness. Historical-frame controls check literal aggregate
fields, fresh names, swapped assignments, both restriction policies and the
single-candidate acceptance boundary. General-validity controls cover both
selected positions, fresh second-voter acceptance, replay/collision rejection
and exact aggregate plaintext. Minimum-recipe controls include a two-node minimum,
semantic E5–E7 cancellation and counterexamples to substituted normality and
raw-normality sufficiency. Selector controls establish minima of one, two and
three nodes under their respective substitutions, retain a fresh accepted
historical context and show a changed outer head after argument normalization.
Decryption path controls cover delayed E5/E6 matching, continued plaintext
reduction, a minimum six-node stuck decrypt, non-normal equivalent wrappers,
and a successful but nonminimum decrypt under the historical nonce-only policy.
Product controls cover mixed constructed/honest leaves, swapped projection values,
repeated plaintext/nonce factors, wrong-key rejection and the one-node published
ciphertext boundary. A successful repeated-component decrypt returns one+one
and is nonminimum. Multiplication controls cover expanding operands, exact
component reconstruction, different keys, unrelated factors, E0-only matching,
passive-head exclusion, zero-as-factor and the normal-target premise. The seeded
gates and backstops pass. Arithmetic controls retain composition expansion,
E3/E4 numeric collapses, zero presence beside a name, passive-head exclusion and
the normal-target premise. Their three seeded campaigns and 256-input backstop
pass; the literal-add-head negative control fails as expected. Checking-path
controls retain both-bit delayed success, full-E bit/binding rejection, E0-only
success, a four-node minimum with reducible handles, and the normal-target
premise. Their three seeded campaigns and 256-input backstop pass; the false
always-retained-head control fails as expected. Projection-chain controls cover
actual tuple tails, reducible aggregate fields, minimum later selectors, swapped
values, chain-derived product leaves, proof/key exclusions and the out-of-range
boundary. Their three seeded campaigns and 256-input backstop pass; literal and
hidden pair fields refute omission of the field premise. The minimum-origin gate
checks finite-catalogue minima for pair/ciphertext/proof values, with independently
varied voter positions and swap bit. Its three seeded campaigns and 256-input
backstop pass. Controls include actual minimum decrypt/projection recipes,
exact mixed/repeated plaintext reconstruction, a reducible target key, honest
proof minima and counterexamples to omitted minimum/frame premises. The
accepted-ballot gate checks all bit vectors at each generated one-through-five
candidate count, field/tail positions and delayed proof binding. Its three
seeded campaigns and 256-input backstop pass. Controls include all-zero
acceptance, two-one aggregate rejection, copied-proof rebinding, tail and
weeding necessity, and a minimum constructed adversarial proof accepted after
both honest ballots. The nonce-fold gate retains repeated factors and
expanding other components across two through five candidates; its three seeded
campaigns and 256-input backstop pass. Complete constructor controls recover
nonce and bit values for both choices and swaps, retain adversarial abstention,
and reject borrowed aggregates despite successful component checks, tail and
weeding. The old selected-index honest-abstention omission remains a checked
control; `GeneralReconstructionSPOT.lean` fills that scope with accepted honest
and adversarial abstention, both swaps and arbitrary valid honest candidates.
The candidate-representation, general-frame and finite-catalogue minimum-origin
gates each pass seeds 1, 7 and 42 (500 configured cases, size 40, `gaveUp=0`)
and 256 backstop inputs. The numeric-interpretation shortcut fails as expected.
There are 76 new public theorem type/axiom audits and 21 definition/field checks.
The static-observation gate also passes seeds 1, 7 and 42 and 256 inputs;
its raw equality proxy is explicitly incomplete for E0-enabled checks. Both
freshness/key-policy defects are detected and retained as full-E counterexamples.
The 24 transfer/control theorems have type and axiom audits. The later numeric-
reflection and honest-combination suites pass the same seeds and backstops,
retaining all three intended failures as kernel controls. The combination gate
uses actual valid general frames. There are 33 new public theorem audits and
ten definition/type checks for that increment. The mixed-ciphertext increment
adds 25 public theorem audits and two definition checks. Its separated-nonce
and mixed-frame gates pass seeds 1, 7 and 42 (500 configured cases, size 40,
`gaveUp=0`) and 256 backstop inputs each; the mixed-frame gate also passes
320 directed inputs covering zero payloads and changed remainders. Both
missing-protection and missing-padding defects are detected at n=0, seed 1,
zero shrinks, and retained as checked controls. The arbitrary-product grouping
increment adds 24 theorem audits and eleven definition/type checks. Its three
seeded campaigns, 256 backstop inputs and all nine directed merge cases pass;
the dropped-public-factor defect fails at n=0, seed 1, zero shrinks. Wrong-key
fusion, deleted factors and inserted zero/unit controls are kernel-checked.
The ciphertext-observation increment adds 21 theorem audits and five definition
checks. Its key-coherence and exact grouped-summary gates pass the same three
seeds, 256 backstop inputs and 576 directed matrix inputs. Omitting a subtree
key comparison fails at n=0, seed 1, zero shrinks. Actual-frame controls retain
all nine case comparisons, changing key values, wrong-key incoherence and an
inhabited minimum-recipe induction interface. The proof-observation increment
adds 20 theorem audits and three fixture checks. Its actual proof-field gate
passes the same seeds and 256-input backstop, plus inputs 160 through 799.
The incorrect component/aggregate tag separation fails at generated input 5
(one candidate), seed 1, zero shrinks. Eight checked controls retain the
boundary equality, freshness, the fourth binding argument and the inhabited
minimum-proof induction interface. The public-key increment adds 22 theorem
audits and five definition checks. Its chain and constructor gates pass the
same three seeds and 256-input backstop, plus a 2400-input sweep covering
all fst/snd words through length four and all three roots at each generated
count/swap. The missing-minimum mutation fails at input 0, seed 1, zero shrinks.
Exact one-/two-node minima, delayed E5/E6 paths and the full-policy distinction
are kernel-checked. The initial-frame partial-decryption increment adds 19
public theorem audits and five definition checks. Both ordered-constructor and
initial-chain gates pass the same three seeds, 256-input backstop and
2400-input directed chain sweep. Argument commutation and omitted minimum size
both fail at input 0, seed 1, zero shrinks. Eight checked controls retain exact
three-node minima, complete-ciphertext binding, delayed paths and the failure
of the origin claim for a frame publishing a partial decryption. The full
six-node minimum-recipe interface is inhabited in a diagonal-candidate frame.
The pair-observation increment adds 21 public theorem audits and four definition
checks. Its tail-identity and constructed-pair gates pass the same three seeds,
256 backstop inputs and a 6760-input directed sweep of all nonempty tail offset
and voter pairs at one through five candidates and both swaps. The omitted-
nonempty mutation fails at input 0, seed 1, zero shrinks. Nine checked controls
retain empty-tail equality, colliding nonces, equal heads at different tail
lengths, reconstruction/truncation, conditional pair eta, nonminimum wrappers,
and all form comparisons. Two one-node ballot handles instantiate the complete
minimum-pair interface in different-vote worlds at the base bound of two.
The atomic increment adds 20 public theorem audits and four definition checks.
Its handle/output and atom-identity gates pass the same three seeds and 784
backstop inputs. Omitted minimum size and collapsed constants both fail at
input 0, seed 1, zero shrinks. Eight checked controls retain nonminimum bit sums,
successful honest checks, the one-candidate empty-tail failure, name wrappers,
policy-sensitive name deduction and the source initial-frame boundary. Two
unequal atomic minima instantiate the full swap theorem without a bounded
premise and retain their values in a changed destination frame.
The destructor-observation increment adds 18 public theorem audits and four
definition checks. Its honest-projection and whole-check/ok gates pass the same
three seeds and 256 backstop inputs. Ignoring the proof argument and omitting
minimum size both fail at input 0, seed 1, zero shrinks. Eight checked controls
retain exact two-node projection and four-node stuck-check minima, the empty-
tail boundary, nonminimum key extraction from a constructed pair, successful-
check collapse to ok, and the probe that detects a newly enabled check. The
complete stuck-check branch is inhabited with a reducible supplied target and
an eight-node bound in diagonal-candidate frames.
The stuck projection/decryption increment adds 17 public theorem audits and ten
controls. Exact two-node projection and three-node decryption minima, reducible
arguments, distinct stuck outputs, full-E honest wrong-key rejection and the
necessity of stuckness/minimum size are checked. The forward interface controls
use diagonal equality instances; they do not establish nontrivial recipe-pair
transfer by testing. The three seeded gates pass 500 configured cases per seed,
size 40, gaveUp=0, and 256 backstop inputs; both omitted-stuckness mutations fail
at input 0, seed 1, zero shrinks. The later value-shape increment closes the
minimum reverse-transfer branches.
The partial-key decryption increment adds 15 public theorem audits and eight
controls. The three-probe characterization retains structured-key E5 and E6's
complete ciphertext binding. Actual six-node minima, unequal observations,
reducible supplied targets and a changed-binding distinguisher are checked.
Both seeded families pass 500 configured cases per seed, size 40, gaveUp=0,
and 512 backstop inputs; both known defects fail at input 0, seed 1, zero shrinks.
The value-shape increment adds 18 public theorem audits and three definition
checks. Seven controls retain actual one/two/three/six-node minima, both complete
stuck-destructor iff branches, unequal outputs and reducible targets. An honest
ciphertext changes its E-value while retaining its shape. Secret-key-policy
and universal-stuckness mutations fail at input 0, seed 1, zero shrinks. The
shape gate passes the three seeds with 500 configured cases, size 40, gaveUp=0,
and 4096 deterministic inputs.
The composition increment adds 25 public theorem audits and seven definition
checks. Eight controls retain reducible factors, reassociation, permutation,
observable duplicate counts, exact three-node minima and the no-zero-unit
boundary. Distinct permuted minima and unequal multiplicity minima instantiate
the complete equality branch. Hidden-composition and duplicate-deletion
mutations fail at input 0, seed 1, zero shrinks. The factor gate passes the three
seeds with 500 configured cases, size 40, gaveUp=0, and 1024 deterministic inputs.
The addition increment adds 27 public theorem audits and four definition checks.
Eleven controls retain numeric presence, exact counts, duplicate atoms, hidden
numeric/additive values, reducible mixed sums, exact three-node minima and the
complete equality branch. One-node numeric minima also instantiate it in
different-vote worlds. Both defects fail at input 0, seed 1, zero shrinks. The
summary gate passes the three seeds with 500 configured cases, size 40,
gaveUp=0, and 5120 deterministic inputs.
The multiplication increment adds 39 public theorem audits and thirteen
definition/field checks. Twelve controls retain required fusion beside a name,
exact final partition cardinality and strict bounds, wrong-key rejection,
hidden-product normalization, repeated factors, retained remainders and the
no-unit boundary. Distinct permuted and unequal multiplicity minima instantiate
the complete equality branch. Both defects fail at input 0, seed 1, zero shrinks.
The partition gate passes the three seeds with 500 configured cases, size 40,
gaveUp=0, and 2048 deterministic inputs.
The 1433 nonempty axiom reports use only `propext`, `Classical.choice` and `Quot.sound`;
another 17 reports are axiom-free.
The variable-overlap gate
passes seeds 1, 7 and 42 plus 256 deterministic inputs; its deliberate
failed-match control is retained as a checked theorem. Public theorem types and axioms are
printed by `ExplainableCrypto/Helios/Symbolic/Audit.lean`.
`python3 scripts/check_helios_claims.py` checks the general reconstruction's
source audit coverage and selected stale status claims; it does not replace
Lean elaboration. No custom axioms,
`sorryAx`, warnings or errors were reported in the final build. Proposal edits
present before the proof work are included at the user's request.
