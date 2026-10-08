# Atomic values after publication

The atomic minimum-observation branch now transfers exact full-E atom values
and their equality tests in accepted expanded frames. It needs no smaller-
observation hypothesis. Published constant-valued result handles are included
alongside literal constants; the initial-frame literal-only classification
does not extend unchanged.

## Checked claims

`expanded_handle_atomic_origin` proves that only result handles can have
atomic values. It excludes the old key, old nonempty ballot tuples and new
partial constructors. This classification itself needs neither numeric results
nor accepted submissions.

With numeric results, `expanded_handle_not_name` excludes name-valued result
handles as well. `expanded_name_deducible_iff` uses published-frame protection
to characterize name deducibility under the actual full restricted-name policy:
a name is deducible exactly when its literal is public. It requires public
submissions, without acceptance or freshness. Combining these facts with a
one-node literal competitor gives `expanded_minimum_name_form`.

`expanded_minimum_constant_form` works under any caller-supplied minimum
policy. Its alternatives are the literal constant or a result handle together
with full-E equality of that result to the supplied constant. It uses the
public literal's one-node size bound and atomic handle classification. It does
not assume numeric results or collapse all numerals to zero/one.

`expanded_minimum_atomic_value_transfer` requires source numeric results,
public submissions and equality of each source/destination result slot. It
preserves the supplied ground atom value modulo full E. The name case is
literal syntax. The constant case is either a literal or a result handle,
whose value follows the shared-result premise.

`accepted_expanded_minimum_atomic_value_transfer` supplies both numeric and
shared-result premises from the accepted-sequence tally theorem. It supports
either source and destination vote assignment. The destination equality
criterion is precisely equality of the supplied atom values, covering all
name/name, name/constant and constant/constant comparisons, including result
aliases. `accepted_expanded_minimum_atomic_equality_swap` closes the atomic
branch without a residual smaller-test or shared-result assumption. It retains
freshness, public submissions, acceptance, source minima and atomic targets.

The conclusion is **equality modulo E**, not literal equality of the raw
evaluated terms. Nor does it permit an arbitrary destination frame with changed
result slots. Those stronger claims have concrete counterexamples below.

## Controls and oracle correction

Eight controls in `ExpandedAtomicSPOT.lean` cover public-name deducibility and
literal minimum syntax together with restricted-secret exclusion; minimum
zero/one result handles that are not literal recipes; a raw-normalized zero
result that remains `0 + 0`; unequal accepted result observations; equal
literal/result aliases; a changed destination result refuting arbitrary-frame
transport; a nonminimum public name wrapper; and a minimum one-node result
handle whose valid tally of two cannot equal any ground atom.

The first positive gate failed at input zero because it compared raw-normalized
results directly to literal zero/one. Inspection showed `0 + 0` and
`(0 + 1) + 0`. Raw normalization handles rewriting but does not canonicalize
these E0 sums. The corrected fixture oracle compares the existing addition
syntax summaries. The raw-result control permanently records the distinction;
the symbolic model and candidate theorem were unchanged.

The corrected gate detects literal-only minimum syntax and arbitrary-
destination transfer mutations at input 0, seed 1, zero shrinks. Seeds 1, 7
and 42 each pass 500 cases at size 40 with `gaveUp=0`; 2048 deterministic inputs
pass. Each input compares eight atomic recipes in all ordered pairs: two
public names, all four constants and both result handles. This is bounded
executable evidence using raw normalization and E0 addition summaries, not a
complete full-E decision procedure.

## Verification and scope

The gate passes 1017 jobs. Targeted origin, transport and eight-control builds
pass 925, 926 and 1024 jobs. Logs are
`tmp/variable-overlap/expanded-atomic-gate.log`,
`tmp/variable-overlap/expanded-atomic-origins-check.log`,
`tmp/variable-overlap/expanded-atomic-transport-check.log` and
`tmp/variable-overlap/expanded-atomic-spot-check.log`.
Full `lake build` passes 3655 jobs, with 1983 nonempty standard-only axiom
reports and 20 axiom-free reports. The checker covers 1017 public theorem
entries and 54 current-status documents. Seventeen new theorem audits include
eight controls. Integrated log:
`tmp/variable-overlap/expanded-atomic-full-build.log`. Four new modules are
`ExpandedAtomicOrigins.lean`, `ExpandedAtomicTransport.lean`,
`ExpandedAtomicSPOT.lean` and `ExpandedAtomicExperiments.lean`.

The source equations and public transcript definitions are unchanged. The
[blueprint](helios-proof-blueprint.md) remains at B8, seven of ten completed
milestones (70% unweighted). Other expanded-value observations, shared minimum
transport, global induction, historical process matching and full symbolic
secrecy remain open.
