# Concrete Helios computational development

Current status: **3/3 computational milestones complete under the revised
boundary; publication package complete**. The completed result combines
checked encoded-attacker coverage and conditional secrecy with the documented
external uniform-efficiency argument. The build split below preserves the
checked native-machine experiments with their individual scope.

`ElectionSecurityFamily.Family.coverage` and `.run_coverage` preserve the original
prepared election and complete shared-cache law. `.ballot_secrecy` proves
negligible original bias under negligible reciprocal field size, DDH, and
`MainReductionEfficient`/`RejectionReductionEfficient` for the exact normalized
fair-bit reductions. `ElectionPublicBounds` derives reached public shapes;
`ElectionPublicEncoding` proves faithful encoding and actual length bounds.
The connection from conventional uniform PPT implementations to the resource
interface and complete reduction efficiency is external mathematics. Lean does
not construct the whole reduction's finite machine in this result.

Navigation: [task list](../../../task%20list.md),
[proof blueprint](../../../docs/research/helios-proof-blueprint.md),
[results](../../../docs/research/helios-results.md),
[closing audit](../../../docs/research/helios-computational-closing-audit.md),
[scope comparison](../../../docs/research/helios-scope-comparison.md), and
[formal reference](../../../docs/formal-reference/main.pdf).
The symbolic and computational repair, rejection and observation definitions
differ; the comparison makes no cross-model correspondence claim.

## Build targets

All source files remain in this directory on the same pinned toolchain. The
[case-study aggregate](../Computational.lean) is the explicit retained-root
manifest: `ElectionSecurityFamily`, `AttackProbability`, `RepairedSampling`, and
35 control roots. Their import closure includes the concrete public attack,
repaired execution/honest correctness, reduction and coverage controls, and all
machine definitions required by `ReductionEfficiency`.

The selection deliberately includes failed repairs (`RepairControls` and
`WeakProofMalleability`), actual shared-cache rejection (`ElectionRepairControl`),
sampling-loss controls (`CoinDenominators`), and cached verification/extraction
controls (`ElectionAcceptance` and `ElectionExtractionBound`). A secrecy-only
closure would omit this evidence. Controls specific to deferred executor/compiler
experiments live in the optional target even when their semantic dependencies
are shared with the case study. Embedded controls in retained files stay retained.

```sh
lake build
python3 scripts/audit-helios-computational.py
python3 scripts/check_helios_targets.py
```

The [optional full aggregate](../Execution.lean), built by `HeliosExecution`,
imports the retained case study and all remaining computational modules:

```sh
lake build HeliosExecution
python3 scripts/audit-helios-computational.py --scope full
python3 scripts/check_helios_targets.py --full
```

The full audit covers the union, not only the deferred complement. Audit logs
are separated under `tmp/computational-audit/case-study/` and `full/`.
`check_helios_targets.py` checks the source partition and the actual loaded Lean
module sets. It writes the exact roots, retained closure and deferred complement
to `tmp/helios-target-split/inventory.json`. Update the appropriate aggregate when
adding a module; new deferred modules must be reachable from the full aggregate.

Build the optional target before the historical execution gates below.
The mathematical reference builds with `--document reference` using the default
target; its companion [historical catalogue](../../../docs/formal-reference/catalogue.pdf)
builds with `--document catalogue` using the optional target. Both options belong
to `scripts/build-formal-reference.sh`. The target split changes no theorem,
hypothesis or source path and does not establish a measured build-time improvement.

## Earlier implementation increments and reusable interfaces

The following descriptions retain their historical proof boundaries and gate
commands. Earlier “open” statements and 2/3 or C1–C12 counts refer to those
checkpoints, not the revised result above.

The completed general native oracle round-trip experiment has checked importer,
framed deterministic segment, actual event and full source-charge theorems.
`NativeRoundTrip.execution_cost` derives `callCost` on every allowed reply branch;
hashes have the existing size limit and both coin values remain.
`NativeRoundTrip.execution_correspondence` and `.native_correspondence` check
the complete event tree and native successor. `.framed_correspondence` and
`.framed_cost` include arbitrary private words without changing the cost bound.
Root integration, complete audits and reviewed reference §14.134 pass. Reproduce
the importer and whole-call controls with
`lake env lean scripts/NativeRoundTripGate.lean`.

The interface starts from canonical finite three-symbol cell storage, original
head registers and blank query-export scratch. It executes query export, actual
reply replacement, old-answer-left/query cleanup and native reply conversion,
then returns to the previously selected live native entry. The continuation is
not executed. Existing encoders, stack/memory frames and return proofs are reused;
there are no ballot/group assumptions. A potential caller is the general native
oracle interface. Whole-program compilation, startup packing, physical live-return
transport, standard-PPT coverage and exact reduction efficiency remain separate.

General query export now has a checked complete execution theorem.
`NativeQueryExportFrame.charged` starts with the actual head register, arbitrary
finite encoded before/after cell lists and arbitrary independent private words.
`.native_result`, `.native_storage` and `.private_retained` identify the native
`readWord`, complete original tape/head, private storage and restored scratch.
The source clock is `2*after.length+6`, with instruction-derived charge at most
`12*after.length+36`; internal blanks stop the query while later data survives.
No correspondence or cost certificate is supplied. Root build, full audits, both gates and reviewed reference §14.133 pass;
this increment is integrated/audited. `scripts/NativeQueryExportGate.lean` runs both
independent campaigns. This operation is general over resident canonical cell
storage; the current one-call experiment adds reply import/dispatch. Complete
native compilation and external startup remain separate. The component
interface/reuse table is in the results ledger under
“General native query export: checked acceptance and interfaces”.

The preceding bounded native compilation experiment has a checked positive
result. `NativeWordCompiler` translates a fixed actual `NativeOracleTape.Code`;
`NativeAdaptiveRun.exact_run`/`.native_correspondence` prove the exact generated
query tree, successful complete state and charge. `NativeAdaptiveCost.within`
and `.physical_run` derive bounded-reply and physical execution costs through
the existing machinery. Private dense before/right words and the complete final
answer are retained; the coin replaces the first answer as specified. Initial
packing/loading and general native/PPT coverage remain open. The root build,
axiom audits, independent generated-code gate and reviewed reference §14.132
pass; this increment is integrated/audited.

The component interface and reuse table is in the results ledger under
“Native compilation acceptance theorem and derived cost”. No ballot/algebra
operation is added by this experiment. Native blank-write and blank-move rejection
controls preserve its representation limit. Reproduce the independent gate from
the repository root with `lake env lean scripts/NativeAdaptiveCompilerGate.lean`.

The bounded execution architecture assessment is complete. The checked
increment is integrated/audited; further protocol construction stops here. The
`PrimeProofRequest` resident executor proves one complete fair-bit request with
original proof/state outputs and derived charge. `PrimeProofRequestReentry`
proves cleanup and nonce preparation; `PrimeRemainingProofRequests` derives both
historical source frames. The combined `PrimeRemainingProofCaller` uses two fixed
framed copies of the same executor definition. Its full-state zero-sum native
test and two fault controls pass. General combined execution/source/cost and physical correspondence now check
in `PrimeRemainingProofCallerRun`; `PrimeRemainingProofSource` identifies the
original proof/state outputs. Final increment audits pass. Full standard-PPT coverage and exact
reduction efficiency remain architectural uncertainties.

All modules here belong to the root Lake project on Lean/Mathlib
4.33.1 and pinned VCVio; the default/optional split is described above. The earlier native-execution assessment recorded 2/3
milestones and 6/12 C-checkpoints (C1–C4 and C10–C11). That historical implementation
count is separate from the revised 3/3 boundary stated above.

Use the [task list](../../../task%20list.md#computational-checkpoints-current-tracking-view)
for remaining work, the [blueprint](../../../docs/research/helios-proof-blueprint.md#computational-proof-dependencies)
for dependencies, and the [results ledger](../../../docs/research/helios-results.md)
for exact assumptions, controls, failed claims and reproduction commands.
The [formal reference](../../../docs/formal-reference/main.pdf) presents the mathematics.

The complete resident p1 commitment continuation now passes targeted execution
checks. `PrimeSecondCommitTail` composes B, canonical `d=c−e`, adjusted beta,
C and D after the previously audited first coordinate A. It preserves all 65
prior words and appends results on 65–69. Actual typed source values derive every
operand, blank workspace, bound and frame. Five native component campaigns and
independent full-state controls pass. `PrimeSecondAllCommitCaller.execution_source`
and `.physical_run` connect the original raw input to that result and derive
total physical cost from blank work with the same bounded adapter on both sides.
All targeted checks, the root build, complete audits, checker tests and reviewed
§14.128/Theorem14.155 (pages172–173) pass; this increment is integrated/audited. The key encoder below advances its
successor. Next are current-state programming and proof return, then the overall proof and later
election. C6 and intended all-PPT secrecy remain open.

The p1 key encoder now has checked resident and original-raw execution with
derived physical cost. `PrimeSecondKeyMachine` frames the existing eight-field
writer, preserves all 70 old words and writes the original flat key on port 70.
Source values derive its workspace, widths and encoding; no presentation or
cost certificate is supplied. The native gate and independent full-state
controls pass. Complete integration audits and reference review pass.

The first p1 commitment remains integrated/audited in §14.127/Theorem14.154
(pages170–172), including its original-raw correspondence and physical cost.
The new tail reuses the same numeric arithmetic without changing its assumptions.

The first programming prefix is `PrimeProgramCaller`: original raw
input through the actual first programming update, including sticky collision
capture, residual cleanup and ordered history prepend. Complete source/state
correspondence and physical execution bounds pass the root build and audits;
reviewed §14.124/Theorems 14.145–14.147 is synchronized. All typed initial
shadow/live states are allowed, and occupied agreeing values still set bad.

The output encoder now passes complete targeted checks. Source interfaces identify the
returned proof and updated saved-state codecs and derive successor size bounds.
The preserving pair writer has complete execution/charge proofs. The fixed
output controller's independent gate passes six canonical cases, ten mutants
and one guard rejection. Complete output execution, source and raw-caller proofs now pass,
with separate words on 48 (proof) and 49 (updated saved state), all preceding
48 words retained, unchanged draw tree and derived total physical bound.
Root build, complete audits, independent controls and checker tests pass.
Reviewed §14.125/Theorems 14.148–14.150 (pages 166–168) is synchronized; the
output increment is integrated/audited. The existing modules below record earlier
component boundaries as well as reusable interfaces.

The second-ciphertext/four-draw prefix now passes the root build and complete
axiom/reference checks. `PrimeSecondTranscriptMachine` reuses the existing
nonce routing, encryption and full-field draws under a derived source frame.
`PrimeSecondTranscriptCaller.execution_source` and `.physical_run` connect the
original raw input to that prefix with derived total cost and full retention of
the first proof, nonce pair and updated state. Independent native mutations and
typed endpoint controls pass. The reviewed reference §14.126/Theorems 14.151–14.153 (pages 168–170) passes; this
increment is integrated/audited. No complete second proof or C6 closure is claimed.

| Entry points | Purpose and boundary |
| --- | --- |
| `AttackGame`, `RepairedExecution`, `RepairedSampling` | Concrete probabilistic attack, repair and honest correctness; blocking the attack alone is not secrecy. |
| `ElectionOracle`, `ElectionCache`, `ElectionReplaySource` | Full prepared-election oracle/state correspondence and actual replay source. |
| `ElectionDDHSource` | Checked finite advantage bound for the original prepared election, including both actual DDH tests and explicit losses. |
| `ElectionPublicBounds`, `ElectionPublicEncoding` | Actual prefix/finish support gives the fixed board and decoding bounds; complete injective public encodings have proved length bounds and specialize to the existing prime codecs. |
| `QueryClock`, `ElectionClock`, `ElectionSecurityFamily` | Query-clock normalization derives global caps and exact original-game/cache coverage from encoded-input resource bounds; `Family.ballot_secrecy` states the final conditional implication. |
| `ReductionEfficiency`, `ElectionSecrecyConditional` | Explicit finite coin-only realization and DDH predicates; main/rejection efficiency remains a theorem hypothesis, justified externally at the revised boundary. |
| `ElectionSecrecyPrototype` | Preserved conditional asymptotic assembly on globally capped families; the newer `ElectionSecurityFamily` derives a suitable family from original input-bounded callbacks. |
| `ElectionDDHFairBits`, `ElectionSecrecyFairBits` | Actual reduction sampling transport, retaining both DDH worlds and derived query budgets. |
| `BitOracleStackFrame`, `CacheHashMachine` | Preserve arbitrary retained data across oracle commands; execute the actual miss sampler after copying its record from caller port 11, with full-state correspondence and derived copy/sampler charge. The complete loaded dispatcher is proved in `CacheHashDispatchRun`. |
| `CacheRoutineCode`, `CacheHashDispatchRun`, `CacheHashDispatchSource` | Original routine adapters and one fixed loaded request, complete hit/miss tree and final state, derived source/physical cost and exact existing-caller observation. The serialized input link is in `CacheRequestMachineRun`; effective continuations remain open. |
| `CacheHashDispatchBounds`, `CacheRequestInputRun`, `CacheRequestMachineRun` | Derive per-request width bounds, parse four serialized fields, check the return flag and execute the complete request from blank physical work storage. Enclosing record construction and adaptive continuation costs remain open; supported-prefix polynomial bounds are in `CacheRequestPrefixBounds`. |
| `SamplerOperands`, `PreparedScalarMachine` | Parse serialized slack/natural operands, execute the uniform upper-bound successor, prepare width tokens and run the sampler; physical startup/compiler premises and combined sampler cost are derived. Complete cache-caller composition remains open. |
| `CoinModuloMachine`, `CoinScalarMachine` | Fixed source program from loaded width/modulus through coins, division and scalar-prefix writing; complete tree, output frame, return behavior, clock and charge proved. |
| `CacheCallerCoins`, `CacheHashCoins`, `CacheHashHandler` | Word-facing handler uses the executed sampler with full answer/cache/log correspondence and sampling error; original exact-uniform handler is retained. Full adaptive host-caller correspondence is integrated/audited; physical compilation and combined costs remain open. |
| `BitOraclePrimitiveBounded`, `BitOracleInitialInput` | Existing physical loop/startup correspondence under explicit source termination, charge and response-width conditions. |
| `NativeOracleTape` | Native interface agreement; its full compiler and intended attacker coverage remain open. |
| `CacheCallerMachineRun`, `CacheCallerMachineSource` | Executed resident entry, unchanged dispatcher and guarded return with private saved data; exact tree/observation and derived local/primitive cost. Actual source operand production and continuations remain open. |

The complete C6 request now executes from one serialized input, with its physical
startup and source/primitive cost derived. Loaded-width bounds retain the public
parameter widths, private sampler record and count-header growth. Root build,
full standard-axiom audit, symbolic/reference gates, eleven kernel controls and
native mutation checks pass. Reviewed §14.106/Theorems 14.110–14.112 (pages
134–136) is integrated/audited. Original request capture/preservation, historical source-budget specialization
and polynomial request bounds now pass root build and exact-name axiom audit
in `CacheRequestPrefixes`, `CacheRequestPrefixBounds` and `CacheRequestPolynomial`.
Independent width/capture mutation controls and reviewed PDF §14.107/
Theorems 14.113–14.114 (pages 136–138) pass; this increment is integrated/audited.
Enclosing record construction and actual decoding/continuation execution remain open. The existing host
caller is still the specification; C6 remains partial.
Other remaining obligations include group/scalar operations, whole algorithm
costs, standard-PPT correspondence and security-family policy. **The all-PPT
computational ballot-secrecy theorem is not complete.** The symbolic endpoint
and independent attack/repair controls are preserved.

From the repository root:

```sh
lake build
python3 scripts/audit-helios-computational.py
lake build ExplainableCrypto.Helios.Computational.CacheHashDispatchControls
python3 scripts/check_cache_dispatch.py
python3 scripts/check_cache_request_input.py --wrapper
python3 scripts/check_cache_request_bounds.py
python3 scripts/check_cache_request_prefixes.py
python3 scripts/check_cache_caller_entry.py
```

The exact-name public-theorem axiom audit passes with only standard Lean axioms. The complete adaptive host-caller specification is integrated/audited,
including reviewed reference §14.102/Theorem 14.104 (page 128). Serialized
preparation and the complete physical sampler are also integrated/audited in
§14.103/Theorems 14.105–14.106 (pages 129–130). Sampling fixtures are
bounded independent checks; the general claims are established by the Lean theorems.


Resident caller entry/return now passes root build and complete standard-axiom
audit, with 525 native mutation fixtures and nine kernel controls. The full
request result and saved word are preserved; reentry on the returned miss result
is checked independently. Source budget and primitive execution bounds retain
old-answer length and saved-data height. Reviewed reference §14.108/Theorems 14.115–14.116 (pages 138–140)
passes; this resident-entry component is integrated/audited. This component does not establish actual source operand
production, response decoding, arbitrary continuations or total adaptive cost.


`PrimeNonceMachine.successor_run` now executes the historical nonzero-nonce
response using the existing parser/incrementer and writer, preserving arbitrary
suffix and three saved words. `.charged` derives the complete instruction cost.
Root build, six kernel controls and the 1,024-case native mutation gate pass;
full standard-axiom audit and reviewed reference §14.109/Theorem 14.117 (pages 140–141) pass; this successor component is integrated/audited. Complete nonce sampling now checks in `PrimeNonceSamplingSource`: executed
q−1 preparation, exact original fair-bit source tree, retained sampling loss,
full state/frame and derived local/physical cost. `NonceOperands` reuses the
existing predecessor and parsed-width region; it adds no arithmetic algorithm.
Native/kernel controls pass; root build, full standard-axiom audit and reviewed reference §14.110/Theorems 14.118–14.119 (pages 141–143) pass; this complete single-nonce component is integrated/audited. The following increment closes nonce-pair
invocation/storage; source arithmetic and adaptive continuations remain open.

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

The nonce-pair components expose the following reuse boundaries:

| Component | Interface and assumptions | Helios dependency and potential caller |
|---|---|---|
| `PrimeNoncePairTransport` | Arbitrary resident record/nonce/context words in the specified eleven-port layouts; exact state, clock and charge. | Port layout chosen for this sampler; uses existing generic copy/frame routines. Both pair entry and reentry call it. |
| `PrimeNoncePairMachine` | Canonical q/slack record; q≥2 for execution, prime q for historical source law; explicit context height. | Nonzero nonce convention and the actual `drawPrimeNoncePair` source. `strongHonestBallotWithNoncesOracle` and `repairedSubmissionWithNoncePairs` are the concrete enclosing callers; their execution is still open. |

These scoped interfaces do not establish framework reuse. A second application
is deferred until the computational secrecy theorem is complete.


The arithmetic components expose these scoped reuse boundaries:

| Component | Interface and assumptions | Helios dependency and potential caller |
|---|---|---|
| `BinaryModMultiplyArithmetic` | Natural reduced addition and bit-fold identities; x,r<p where needed. | No protocol dependency. Supplies the executed multiply invariant and prospective power loop. |
| `BinaryModAddMachine` | Canonical r, p−x and p digits with x,r<p; full result, retained operands and derived charge. | No cryptographic assumption. The multiplier prepares the complement and calls this controller. |
| `BinaryModMultiply` | Loaded canonical x/p, x<p, arbitrary little-endian multiplier word; full cleanup and width-based charge. | No protocol dependency in the execution theorem. Square-and-multiply is the next concrete caller. |
| `BinaryModMultiplySource` | Group-coordinate equality for p≠0 and a derived physical run from lowered resident ready state with empty auxiliary oracle tapes. | `PrimeGroup` represents public multiplicative residues using additive notation. Honest encryption is the intended source caller; actual routing and exponentiation remain open. |

These results do not claim arbitrary input parsing or a reusable election
framework. Existing finite-coordinate, frame and return interfaces are reused.

Power and ciphertext interfaces retain these assumptions and potential callers:

| Component | Interface and assumptions | Helios dependency and potential caller |
|---|---|---|
| `BinaryModPowerArithmetic` | Square/conditional-product step and reversed-bit fold; p≥2 justifies literal one. | No protocol dependency. Supplies the executed power loop invariant. |
| `BinaryModPower` / `Run` | Canonical reduced base, p≥2, arbitrary exponent and saved context; complete state and derived cost. | No cryptographic hardness premise. `PrimeEncryptMachine` invokes it twice. |
| `BinaryModPowerSource` | Prime p and q≠0 for historical scalar action; physical run from resident ready state with empty auxiliary tapes. | Existing `PrimeGroup` public coordinates and scalar-value exponent. No discrete logarithms exposed. |
| `PrimeEncryptMachine` / `Run` / `Source` | Canonical reduced g/pk/p, p≥2, arbitrary nonce/context and one-bit vote; full executed state/cost. Source uses prime p/q and actual group-coordinate inputs. | Actual `encryptWith` both coordinates. The honest proof-request constructor is its intended caller; public parsing and nonce-pair routing remain open. |

These interfaces support the concrete case study. A second application remains
required after secrecy before claiming a reusable framework.


The programmed-transcript prefix exposes the following concrete interfaces.
These are scoped components; the second-application requirement still applies.

| Component | Interface and assumptions | Helios dependency and potential caller |
|---|---|---|
| `PrimeFullFieldSource` | q≠0; exact ZMod fair-bit scalar encoding and four-draw source tuple. | Existing VCVio sampling instance; `ballotFullSimTranscript_factor` identifies this tuple with the selected Helios simulator. No commitment execution or ideal-uniform claim. |
| `PrimeHonestTranscriptMachine` | Canonical resident q/slack record, q>0, fixed23-port layout and arbitrary retained words; full run/source/derived charge. | Reuses framed `CacheHashMachine.sample_run`. The four-draw controller is its current caller; another caller must supply the same canonical record/layout. |
| `TranscriptScalarSave` | One of three fixed destinations, source prefix and modulus workspace, arbitrary retained frame; consuming transfer/clear, full state and derived charge. | No cryptographic assumptions; fixed23-port layout matches the transcript constructor. It reuses the existing transfer rather than introducing a new copy procedure. |
| `PrimeTranscriptDraws` | q>0, canonical record and retained words; four successive samples, three actual saves and combined cost. | Stores c/e/z0/z1 for the exact programmed simulator. Raw caller derives all entry words; future commitment code consumes the stored tuple. |
| `PrimeHonestTranscriptCaller` | Primes p/q, typed g/pk, vote/slack/private saved word; original raw input and blank work. | Executes initialization, both nonzero nonce draws, first ciphertext and four field draws. Source equality and physical cost are derived; key generation, later commitments/programming and full attacker execution remain open. |

The source identities preserve complete query trees of `runFairBitUniform`.
Existing approximation losses still separate that implementation from ideal
uniform sampling. Complete private configurations are proof observations, not
additional protocol publications.

The first simulated commitment uses the following existing interfaces and
concrete caller connection. Its execution does not close C6 or establish PPT
secrecy.

| Component | Interface and assumptions | Helios dependency and potential caller |
|---|---|---|
| `ScalarComplementMachine` / `Run` | Canonical q and scalar prefix U(e), e<q; executed decoding/subtraction, complete frame and actual charge. | Natural arithmetic only. Could supply bounded complement operands to other power callers. At e=0 it returns q, not canonical scalar negation. |
| `PrimeSimCommitSource` | Typed q-root subgroup; q prime and p≠0 for the residue-value formula. | Identifies the actual first `ballotSimCommit` coordinate. No exact-order or new hardness assumption; arbitrary residues do not satisfy this identity. |
| `PrimeSimCommitMachine` / `Run` | p≥2, reduced g/alpha and e,z0<q, exact reached input shape with arbitrary retained frame. | Fixed Helios scalar/ciphertext layout; appends15 private ports and returns them empty. Reuses parser, subtraction, transfer, two powers and product. The other commitment coordinates require their own operand/source derivations. |
| `PrimeSimCommitMachineSource` | Prime p/q, typed g/pk, actual prior source tuple and saved word. | Derives every operand and bound from the completed transcript caller's result; complete output is the actual first commitment coordinate. |
| `PrimeSimCommitCaller` / `Run` / `Source` | Prime p/q, typed g/pk, vote/slack/saved word; original raw input and blank work. | Composes the unchanged nonce/transcript draw tree with that coordinate and derives full charge and physical execution with the combined controller's own compiler factor. Subsequent proof construction remains open. |

`PrimeHonestTranscriptCaller.run_support` exposes its existing leaf-bound proof
for this actual composition. The finite code and hypotheses are unchanged.
These interfaces serve the concrete case study; a second application remains
required before any framework claim.

The zero-branch pair reuses that numeric controller through a fixed port map.
Its source theorem keeps the original honest statement; exchanging g/pk in the
first source wrapper would change that statement and is not a valid adapter.

| Component | Interface and assumptions | Helios dependencies and potential callers |
| --- | --- | --- |
| `PrimeSimCommitSecondSource` | Typed q-root subgroup, prime q and p≠0 for the value formula. | Actual second zero-branch coordinate z0·pk−e·beta; no exact-order assumption. |
| `PrimeSimCommitSecondMachine` / `Origins` / `MachineSource` | Actual first-coordinate source result, prime p/q and typed g/pk; all inputs, reduced bounds and blank work derived. | Fixed39-port relocation preserves original38 words, retains first output3 and writes second output38. Reuses the same numeric clock/charge and exact frame transport. A future caller with another layout needs its own presentation proof. |
| `PrimeSimCommitPairCaller` / `Run` / `Source` | Original raw input and blank work, prime p/q, typed g/pk, vote/slack/saved word; same bounded adapter on both sides. | Both zero-branch coordinates follow the unchanged nonce/transcript draw tree. Complete cost uses this combined controller's own compiler factor. The following components complete one-branch subtraction and adjusted-base execution; statement encoding and programmed-state updates remain open. |

The remaining commitment values use the same numeric controller after actual
challenge subtraction and adjusted-base construction. Common components retain
explicit interfaces; the fixed Helios layouts below are concrete adapters.

| Component | Interface and assumptions | Helios dependencies and potential callers |
| --- | --- | --- |
| `BinaryModAddMachine.difference_run` / `.difference_charged_source` | Canonical c/e digits below q; scalar specialization only needs q≠0. Same original program, clock and charge cap. | Generic modular difference; its separately proved zero endpoint avoids the false reduced-complement premise. Any canonical scalar caller can use it after deriving its input digits. |
| `ScalarDifferenceMachine` / `Run` | q≠0, encoded c/e; copies, parses, subtracts, writes the exact prefix, preserves inputs and clears work. | Uses existing copy/parser/difference/writer routines. Potential callers need these same canonical scalar-prefix interfaces; no arbitrary parser/compiler is assumed. |
| `PrimeSimDifferenceMachine` / `Origins` / `MachineSource` | Actual zero-branch source result, prime p/q and typed g/pk. | Derives all operands/workspace; places d prefix on1 and preserves both commitments. Its raw Caller derives complete startup/source/physical cost. |
| `PrimeAdjustedBetaMachine` / `Run` | Numeric p≥2, reduced g/beta, loaded q−1 digits and arbitrary retained frame. | Fixed port maps read existing operands directly; one power/product and two actual guards derive gamma. Numeric q need not be prime. |
| `PrimeAdjustedBetaOrigins` / `MachineSource` | Actual reached difference result and typed subgroup operands, prime p/q. | Derives every operand and identifies actual beta−g, retaining d and earlier commitments. |
| `PrimeSimOneFirstMachine` / `PrimeSimOneSecondMachine` | Actual previous source result, prime p/q, typed g/pk, original vote/slack/saved word and source tuple. | Fixed42/43-port frames reuse unchanged numeric543 controller. They derive d/z1/g/alpha or d/z1/pk/gamma, preserve earlier state, and reuse exact numeric charge. |
| `PrimeSimOneTail` / `Source` | Actual reached difference source result; no caller-supplied frame, source or cost certificate. | Composes adjusted beta and both one-branch coordinates with complete finite return states and derived charge. |
| `PrimeSimAllCommitCaller` / `Run` / `Source` | Original canonical raw input and blank work, prime p/q, typed g/pk, explicit vote/slack/saved word. | Exact unchanged sampling tree and all four actual ballotSimCommit coordinates; physical result uses the same bounded adapter on both sides and the new code's own compiler factor. The following key serializer consumes these coordinates; programming and subsequent ballots remain open. |

These interfaces establish this concrete constructor prefix. The second-application
reuse test remains deferred until the concrete secrecy theorem, before any claim
that these adapters form a reusable framework.


The hash-key constructor serializes the eight reached coordinate words in
`ballotKeyRecord` order. Source, numeric field and complete local key targets
pass, including the raw caller target. Root build, complete audits and the
reviewed formal reference pass; this increment is integrated/audited.

| Component | Interface and assumptions | Helios dependencies and potential callers |
| --- | --- | --- |
| `NatFieldWriterMachine` / `Run` | Canonical `n.bits`, arbitrary suffix, and five blank work ports; retains the original digits and prepends `U(length(U(n))) ++ U(n)` to the suffix. `run`, `padded_run` and `charged` derive complete state and charge ≤32 times `clock n`; `clock_mono` supplies the enclosing modulus bound. | No group, protocol or hardness assumptions. Reuses the existing two-pass copy and both entries of `FrameWriteMachine`. Immediate caller: the eight fixed full-key coordinate fields. Other numeric record callers must establish canonical digits and this workspace layout. |
| `NatFieldWriterMachineControls` | Four literal complete-state positives, including zero and binary-width boundaries; five actual command mutations and a failed-entry rejection control. | Checks source/suffix preservation, both framing layers, cleanup and the entry guard. The independent gate is `python3 scripts/check_nat_field_writer.py`: 33 directed/seeded cases, seeds 118/606/20260914, five mutations, original clock and local-cost cap. |

Here `U` is the existing `uniformNatEncode`; the outer prefix records the
length of the encoded coordinate, not the coordinate value or digit width.
The numeric clock is `5*n.size + 8 + FrameWriteMachine.cost (2*n.size+1)`.
The complete local serializer derives its eight operands from the actual
`PrimeSimAllCommitCaller` result and writes the fixed count while preserving
all 43 old words. The following interfaces connect this local result to its
checked raw caller.

| Component | Interface and assumptions | Helios dependencies and potential callers |
| --- | --- | --- |
| `PrimeSimKeySource` | Prime p/q, typed g/pk and the actual prior source tuple. Derives coordinate digits, p-based widths and empty work 23–27. | Exact original key order `[g,pk,alpha,beta,A,B,C,D]`; group encoding is U(residue), with an outer length frame. This statement is specific to the reached Helios layout. |
| `PrimeSimKeyMachine` / `Run` | Eight canonical natural coordinates below p, five empty reused work ports and arbitrary retained 43-word state; complete output and actual charge. Clock `8*NatFieldWriterMachine.clock(p−1)+1`, charge≤32*clock. | Eight fixed field calls prepend in reverse order, then write U(8). All43 old words are retained and output on port 43 contains the flat key. Reuses the existing finite-frame and live-return machinery. Another eight-field caller needs its own source/presentation proof. |
| `PrimeSimKeyMachineSource` | Prime p/q, typed g/pk, vote/slack/saved word and the actual source tuple; no caller-supplied operand, workspace or cost premise. | `charged_source` and `source` derive complete execution to the original `ballotKeyBitCodec` of the actual statement/commitment. The raw key caller consumes this source theorem. |
| `PrimeSimKeyMachineControls` / `PrimeSimKeySourceControls` | Three independent literal complete 44-port result controls; source-coordinate/byte controls; actual final-step wrong-count and context-corruption controls. | `scripts/check_prime_sim_key.py` passes five source-consistent plus three seeded serializer-only cases, seven actual mutants and an entry rejection. Full state, zero queries, residual tape and original caps are checked; seeded serializer cases do not claim reachability. |
| `PrimeSimKeyCaller` / `Run` / `Source` | Original canonical raw input and blank work, prime p/q, typed g/pk, vote/slack/saved word; same bounded adapter on both sides. Root build and complete audits pass; this caller is integrated/audited. | Derives the actual live return, unchanged fair-bit nonce/transcript source tree and exact key on port 43 with all 43 prior words retained. Complete charge is the prefix plus local key charge; physical cost uses this combined code’s own compiler factor. Programming and subsequent ballots remain open. |

Local and raw targets, root build and complete standard-axiom audits pass.
Reviewed reference §14.122/Theorems 14.139–14.141 (pages 161–162) is
integrated/audited. Key construction itself makes no cache query or state update. The subsequent
programming increment below executes the separate nested-history and sticky
state transition. Later ballots, effective continuations and complete adaptive
cost remain open. C6/C7 and all-PPT secrecy are incomplete;
the required second-application reuse test remains after secrecy.


## Programmed-state extraction interfaces

The complete raw caller now extracts the original shadow cache, separate live
cache, flag and ordered history. Source/execution/physical-cost checks, root build, complete standard-axiom and
symbolic/reference audits, independent controls and checker tests pass. The
synchronized reference §14.123 records the integrated result.

| Component | Interface and assumptions | Helios dependencies and potential callers |
| --- | --- | --- |
| `PrimeFirstProgramSource` | Exact source bind/lift and first-request factorization for arbitrary finite shadow/live states; prime q, group/module instances, and original source continuation. | `source_eq`/`submission_run` retain Alice's remaining proofs, all verifications, Bob and attacker. Empty initialization is a corollary. Narrow bind/lift laws expose existing private interfaces; no new source language or compiler. |
| `PrimeProgrammedStateSource` | Typed finite states, prime p/q, g/pk, vote and original draw tuple. Derives the existing nested codec, retained raw context and blank work; `submission_draw_source` identifies the exact joint draw tuple and actual programmed key. | Specific to the first Helios simulator prefix. It does not prove that an enclosing machine serialized the typed state. |
| `PrimeProgrammedStateInputMachine` / `Run` | Canonical five-field raw record on 14, nested state pairs with singleton Boolean flag, and empty work 23–27; arbitrary other words. Returns shadow/live/flag/history on 44–47, retaining all previous 44 words and clearing work. | Reuses the original copy and field-parser routines. Clock `11*(3*N.size+7+N*(2*N.size+3))+6*N+41`, charge≤32*clock; clock≤`22*N*N+72*N+118`. The fixed schema/layout is Helios-specific; another caller must establish this schema and memory presentation. No semantic validation of arbitrary cache payloads is claimed. |
| `PrimeProgrammedStateInputSource` | `charged_source` derives all numeric parser premises from the actual key-caller result with typed saved state. No supplied origin, workspace or cost certificate. | Original shadow/live cache codecs, singleton flag and nested ordered-history codec. Immediate caller is `PrimeProgrammedStateCaller`. |
| `PrimeProgrammedStateCaller` / `Run` / `Source` | One original canonical raw input, blank initial work, arbitrary typed finite state/live cache, prime p/q, typed g/pk and same bounded adapter. | Actual live return, exact unchanged fair-bit draw tree, full state outputs and retained words, total charge and physical startup/execution bound with its own combined compiler factor. The following programming transition is integrated below; enclosing successor execution remains open. |
| `CacheInsertOccupiedRun` / `Controls` | Canonical occupied cache/key, proposed and existing scalar, and actual lookup equality; full result and actual charge with arbitrary three-word frame. | Original insertion code unchanged. The unread tail, positive counter and old encoded answer persist; capture collision status and clear local ports 0/4/5 before reuse. Another insertion caller can use this full-state interface and must execute its own cleanup. |

The actual-code extractor gate passes 11 canonical nested cases, nine command
mutants and six malformed/guard cases at original clocks/charges. Its arbitrary
payload fixtures validate extraction only. Separate kernel controls derive a
full 48-word result from independent numeric records with unequal nonempty
caches, true bad and repeated ordered history. Existing independent attack,
repair and symbolic controls are unchanged.

At the extraction boundary, collision cleanup, sticky flag/history updates,
proof encoding, repacking and successor execution were pending. The following
programming increment closes the local state update; complete output execution/source/physical checks and integrated audits now
pass below. The full election
also has an auxiliary-domain cache outside this ballot-state codec; the enclosing
frame must retain it. This increment does not close C6 or all-PPT secrecy, and
makes no second-application framework reuse claim.


## Programmed update and encoded-return interfaces

The programmed update is integrated/audited in §14.124. It preserves the
original source tree and independent controls. Its runtime successor matches
`state.program`; its returned proof is the next serialization obligation.

| Component | Interface and assumptions | Helios dependencies and potential callers |
| --- | --- | --- |
| `PrimeProgrammedInsertInputMachine` / `Run` | Full 48-port copy/clear from shadow 44 to input 23, scratch 24 blank; derived uniform charge from original cache length. | Existing copy/return machinery and the concrete resident layout; prepares programming insertion. |
| `CacheProgrammedInsertMachine` / `Run` | Typed cache/key/value, sticky flag and retained live/history words; captures collision before clearing insertion residue and derives complete state/charge. | Existing cache insertion and codec; occupied agreeing values retain cache order and set bad. Potential later programming calls need their actual operand origin. |
| `PrimeProgrammedInsertSource` / `PrimeProgrammedInsertMachineSource` | Prime p/q and actual reached typed state; derives loaded words, seven blank work ports and original-input bounds. | Concrete key/challenge and separate shadow/live states; supplies insertion and history callers without a presentation/cost certificate. |
| `PrimeProgrammedHistoryMachine` / `Run` / `Source` | Canonical bounded numeric statement fields and ordered encoded history; source derives these from post-insertion state. | Builds the original nested statement, increments the count and prepends with duplicates retained; updates only history 47 and restores workspace. |
| `PrimeProgramMachine` / `Run` | Actual reached 48-port state; all preparation/insertion/history premises and total charge are derived. | Executes the complete first programming state transition; later calls must derive successor bounds. |
| `PrimeProgramCaller` / `Run` / `Source` | One canonical original raw input and blank work, prime p/q, typed g/pk, arbitrary finite initial shadow/live state. | Exact unchanged draw tree, final state and complete physical bound using this code's factor. Does not execute the remaining source continuation. |

The following output components retain the original proof and state codecs.
The pair writer, complete output-controller Run/Source and raw-caller
Run/Source targets pass with standard axioms. Root build, complete audits,
independent controls and reviewed §14.125 pass; this increment is integrated/audited.

| Component | Interface and assumptions | Helios dependencies and potential callers |
| --- | --- | --- |
| `BitPairWriterMachine` / `Run` | Arbitrary input words, blank output/four work words and success memory. Returns `F[a,b]`, retains inputs, restores work; actual charge is at most 32 times its derived clock. | Reuses copy and field writers; no cryptographic assumptions. Supplies existing nested codec constructions. Another caller must prove its framing and length bounds. |
| `PrimeProgramProofSource` | Prime p/q, actual source tuple and reached programming result; derives exact returned proof, coordinate/scalar words and widths. | Zero branch `(A,B,e,z0)` and one branch `(C,D,c-e,z1)` in the existing seven-pair proof codec; potential later `p1`/`pt` encoding after their own execution. |
| `PrimeProgramRepackSource` | Same actual source, arbitrary finite initial states; derives next cache/history counts at most original raw length `N+1`, retained live count at most `N`, and exact three-pair saved codec. | Preserves live/shadow distinction and repeated history; proves every updated saved word differs from the old one. This is source/size algebra, not an executed successor. |
| `PrimeProgramOutputMachine` | Fixed controller with four numeric-field calls, eight preserving-pair calls and eight temporary clears. Original-code gate, complete Run/Source targets and integration audits pass. | Actual full output 48 = original returned proof, 49 = updated both-cache state, all prior words retained. No extra encoded pair joins these outputs. |
| `PrimeProgramOutputCaller` | Checked composition framing the existing raw prefix with two blank output ports, then returning to the actual encoder entry. | Exact unchanged draw-source tree, both encoded outputs, retained words and derived total charge/physical bound are integrated/audited. |

The pair writer clock is
`2*(L+R)+FrameWriteMachine.cost L+FrameWriteMachine.cost R+7`.
The output clock sums four natural-field writer bounds, eight pair-writer
bounds, eight temporary lengths and eleven fixed steps. Source bounds retain
p-based group coordinates, q-based scalar words and actual updated record sizes.
The original raw context on 14 remains unchanged; the new saved word on 49
must be handed to the actual continuation. That continuation preserves both
nonces and `p0`, requests `(false, rs.2)` then `(vote, rs.1+rs.2)`, and permits a
zero sum. Restarting the entire raw prefix would resample and repeat `p0`.
Later ballots, verification, the effective attacker interface and complete
adaptive costs remain open. The auxiliary-domain cache still needs its enclosing
frame. C6 remains partial; no general compiler, all-PPT secrecy theorem or
second-application framework claim follows from this local encoding work.


### Retained second-nonce continuation

| Component | Interface and assumptions | Helios dependency and potential caller |
| --- | --- | --- |
| `PrimeRemainingProgramSource` | Prime moduli, typed public inputs, arbitrary nonce pair/first proof/states and source continuation; exact two-request source equality. | Uses `(false,r2)` followed by `(vote,r1+r2)`, including zero sums, and the original programming handler. Supplies the semantic specification for Alice's remaining proof requests. |
| `PrimeSecondTranscriptSource` | Derives inputs, empty work, frame and widths from the actual first returned-proof state. | Retains the original nonce pair and proof, and uses updated saved49 while raw14 still holds old state. No caller-supplied presentation premise. |
| `PrimeSecondTranscriptMachine` / `Run` | Canonical g/pk<p, p≥2 and nonce n<q; arbitrary retained words/frame. Actual code and four fresh word draws with derived full state and branch charge. | Fixed second-component vote and resident mapping; numeric routing, encryption and sampling are reused. The next commitment prefix consumes these outputs. |
| `PrimeSecondTranscriptMachineSource` | Derives every numeric premise from the typed source; exact fair-bit tree and support halt/cost. | Ends before second commitments, programming and returned-proof encoding. It does not assume those operations have executed. |
| `PrimeSecondTranscriptCaller` / `Run` / `Source` | One original canonical raw input, blank work, actual prefix/successor composition and derived physical startup/total cost. | Reuses the sampled pair and first proof, then samples only the second transcript tuple. Later election and effective-attacker execution remain open. |

Run `python3 scripts/check_second_transcript.py` for the complete native campaign;
`--seeded-only` reproduces the isolated seeded partition. The checked evidence
covers eight distinct fixtures, nine mutations and one guard rejection across
the retained directed/mutation results and seeded replay. The earlier 120-second
host timeout stays recorded as an incomplete campaign; the seeded replay passes
with 300 seconds, identical code/driver hashes and original modeled caps. No
additional whole-raw native campaign is claimed. Typed endpoint controls preserve
independently specified values and distinguish nearby incorrect results.


### Remaining second-proof commitments

| Component | Interface and assumptions | Helios dependency and potential caller |
| --- | --- | --- |
| `PrimeSecondCommitBMachine` / `Source` | Prime p/q, typed g/pk, arbitrary initial states and actual nonce/transcript tuples; full source-derived entry/exit, actual charge and retained old65 state. | Unchanged numeric commitment code reads pk/beta1 and fresh e/z0; writes B on65. Its immediate caller is the p1 commitment tail. |
| `PrimeSecondDifferenceMachine` / `Source` | Actual B result supplies q bits, fresh c/e prefixes and blank work; derives canonical `(c−e).val`, full state and original scalar-controller charge. | Fixed67-port frame retains old66 words and writes U(d) on66. Uses existing subtraction and codecs; another caller needs its own reached-state presentation. |
| `PrimeSecondAdjustedMachine` / `Source` | Actual difference result supplies beta1/g and retained `(q−1).bits`; typed prime-group inputs discharge numeric power/product bounds. | Fixed68-port frame preserves old67 words and writes beta1−g on67. Raw14 is retained, not reparsed during this arithmetic stage. No new inverse algorithm or arithmetic premise. |
| `PrimeSecondOneFirstMachine` / `Source` | Actual adjusted state supplies g/alpha1/d/z1; full source-derived frame and numeric bounds, including d=0. | Unchanged commitment code writes C on68 while retaining old68 words. Exponent q when d=0 follows the existing subgroup law. |
| `PrimeSecondOneSecondMachine` / `Source` | Actual C result supplies pk/gamma1/d/z1 with no caller-supplied origin or cost certificate. | Writes D on69, preserving old69 words. All four coordinates equal the original `ballotSimCommit` fields for `(false,r2)` and fresh transcript scalars. |
| `PrimeSecondCommitTail` / `Source` | Actual A result with arbitrary typed source tuple/states; derives all five successful returns and complete execution charge. | Query-free tail preserves all old65 words, with cost `96*K + S + 32*G` for commitment clock K, scalar difference cost S and adjusted-base clock G. |
| `PrimeSecondAllCommitCaller` / `Run` / `Source` | Original canonical raw input, blank work, prime p/q and arbitrary typed finite states. Exact source and physical-cost targets pass; root build, complete audits and reference review pass. | Derives the exact original nonce/first-transcript then fresh second-transcript tree, retained first proof/state and physical cost using this code's compiler factor. Remaining p1 serialization/programming/return is not supplied by arithmetic alone. |

Reproduce the five new component gates after `lake build`:

```sh
python3 scripts/check_second_commit_b.py
python3 scripts/check_second_difference.py
python3 scripts/check_second_adjusted.py
python3 scripts/check_second_one_first.py
python3 scripts/check_second_one_second.py
```

B, difference and adjusted beta each have nine canonical fixtures; C/D each
have seven. Every campaign has one guard rejection. B/C/D have eight instruction
mutants, difference six, and adjusted beta seven. The
three seeds are 118/606/20260914. Full resident states, zero queries, residual
stream and original clock/charge caps are checked. The labeled zero-nonce case
is a numeric boundary outside the original nonzero sampler support; source-shaped
fixtures do not claim empty-election reachability. Typed full-state controls
independently check `(A,B,d,gamma,C,D)=(6,13,10,2,2,2)` at p=23/q=11 and retain
p0/raw/saved/nonces across all occupied/bad combinations. These controls and the
actual component traces are separate from the composed general theorem; no
additional whole-raw native campaign is claimed. The second-application reuse
check stays after the concrete secrecy theorem.


### Second-proof key serialization

| Component | Interface and assumptions | Helios dependency and potential caller |
| --- | --- | --- |
| `PrimeSecondKeyMachine` / `Source` | Prime p/q, typed g/pk, arbitrary finite initial states and both source tuples. Actual source values derive canonical coordinates below p and empty work23–27; `charged_source` preserves all 70 old words and writes the key on port 70 with cost≤32*clock. | Fixed frame of unchanged `PrimeSimKeyMachine`; key order is `[g,pk,alpha1,beta1,A1,B1,C1,D1]`. Clock is `8*NatFieldWriterMachine.clock(p−1)+1`. The second programming caller consumes this result; other layouts require their own checked source presentation. |
| `PrimeSecondKeyCaller` / `Run` / `Source` | One original canonical raw input and blank work, prime p/q and arbitrary typed finite states. Targeted exact source and physical-cost checks pass. | Same original nonce/p0 tuple and fresh p1 tuple; full 71-word output and actual prefix-plus-key cost with this code's own compiler factor. Key serialization makes no cache query or programming update. |
| `PrimeSecondProgramSource` | Same typed source; `source_fields/work/statement/context` derive the actual key, challenge, separate caches, flag, history and seven blank work words. Current cache/history counts are bounded by `N+1`; semantic next counts by `N+2`. | Original first-update successor and p1 programming semantics, including agreeing collisions and repeated history. Supplies the next insertion/history caller; it does not execute that update or return encoding. |
| `PrimeSecondKeyControls` | Independent complete 71-word fixture across four occupied/bad combinations, actual execution via the checked theorem, and wrong-key/order/framing and command-mutation controls. | Literal flat fields `[2,4,2,4,6,13,2,2]` at p23/q11; preserves prior proof, current saved state, nonces and original raw input. |

Reproduce the native gate after `lake build`:

```sh
python3 scripts/check_second_key.py
```

Seven source-shaped fixtures and nine actual instruction mutations plus one
entry rejection pass at seeds 118/606/20260914, with zero discards/gaveUp. Full 71-word
states, zero queries, residual bits and original tick/charge bounds are checked.
The raw composition has checked code/return identities; no additional whole-raw
native campaign is claimed for that earlier wrapper. Complete integration
audits and reference review pass. The shared resident executor now executes p1
and the overall proof, with exact original-source outputs and derived combined
cost. Later election execution remains open. C6 remains partial and the
second-application reuse check stays after concrete secrecy.
