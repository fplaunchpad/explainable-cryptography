# Publication values and existing handles

Current update: [local rigidity](helios-source-local-rigidity.md) refutes the
Extended normalization implication from WellFormed/nonempty full class alone.
The counterexample also has an embedded joint opening; Named.Structural
separation and a sufficient reconstruction invariant remain open.

Status: **machine-checked** for reached elections with fresh names. B9/B10
remain incomplete at 8/10 unweighted milestones (80%).

Every public publication in a reached election differs modulo full E from all
previously exported handles. Consequently, an arbitrary raw process with the
maintained joint election invariant cannot perform an existing-handle free
output. This discharges the election-level old-domain obligation left by the
[generic output closure](helios-source-handle-output.md).

## Evidence and hypotheses

`SourcePublicationSeparation` proves the value distinctions:

| Publication | Previously exported values | Separation evidence |
| --- | --- | --- |
| First ballot | Public key | Tuple versus public-key constructor |
| Second ballot | Key and first ballot | Constructor shape and fresh voter nonces |
| Trustee partials | Key and both ballots | Candidate tuples have n+1 cells; ballots have 2(n+1)+1 |
| Results | Key, both ballots and partial tuple | Tuple length; numeric results versus partial-decryption constructors |

`fresh_ballots_distinct` uses the first ciphertext and injective voter nonce
allocation; candidate values may coincide. `candidateTuple_not_ballot` uses the
existing general full-E tuple-length theorem, including arbitrary field
reductions. `candidateTuple_not_initial_handle` covers all three initial handles.
`source_results_not_partials` projects the first candidate and uses a numeric
result premise to exclude a partial-decryption value.

`Publication.old_handle_distinct` discharges that numeric premise from actual
reachability: the reached history is public and accepted, and the existing
tally theorem supplies numeric results. It quantifies over every old handle
and all four Publication constructors. Fresh names and reachability remain
explicit premises; no search failure or normalization heuristic is used.

`SourceElectionHandleExclusion.source_coordinated_no_handle_output` takes a raw
joint relation to a reached election in arbitrary base/channel permutations.
An assumed actual FreeStep output reflects to a complete canonical visible
message equal to its old handle. Public-channel reflection and exhaustive
publication classification identify a Publication, contradicting the value
separation theorem. All channels and raw targets are quantified; no Structural
presentation or action reconstruction premise is added.

`source_joint_no_handle_output` specializes to identity coordinates.
`CoordinatedPhaseOpening.no_handle_output` additionally handles the invariant's
explicit equality between the raw and phase handle domains. Channel freshness
is not needed for this exclusion: it uses the actual public-channel policy and
the existing public-output classification. Other correspondence results retain
their own channel-freshness requirements.

## Controls and correspondence

`SourceElectionHandleSPOT` has thirteen public kernel controls. They cover all
old handles at each of the four live publication phases in both vote worlds.
Actual bound-output derivations remain available at all four phases under
nonidentity name coordinates. Result old-handle output is rejected for every
channel and raw target. Parallel padding exercises a noncanonical second-ballot
source endpoint.

The negative fixture assigns the same nonce to both voters and the same
candidate values. Their whole ballots then coincide, refuting unconditional
publication separation. The fixture is proved non-fresh, and a real Out-Atom
output of the colliding stored value remains derivable from a corresponding
canonical prefix. That last fixture is a prefix control, not a claim about a
complete execution of the malformed election.

The reality oracle is the source's four complete bulletin-board publications
and Figure 3's Out-Atom rule. Full E/E0, SPK fourth fields, structured-key E5,
full-ciphertext E6 and the original public observations remain unchanged. The
new proofs compose existing general separation/classification results with
directed kernel controls; no randomized cryptographic campaign is claimed.

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

## Remaining obligations

The existing-handle election case is closed by exclusion. Construct matching
actions in arbitrary related raw counterparts and establish raw bound-output
frame Structural presentation, then assemble the paired relation and all weak
labelled bisimulation/secrecy clauses. Canonical matching actions alone do not
discharge the arbitrary raw counterpart obligation. The joint semantic relation
does not imply a Structural presentation or raw StaticEq witness.

See the [blueprint](helios-proof-blueprint.md),
[task list](../../task%20list.md) and [results ledger](helios-results.md).
