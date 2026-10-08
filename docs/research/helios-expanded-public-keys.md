# Public-key values after publication

The expanded published-frame proof now classifies minimum public-key values,
excludes constructed aliases of the election key, and proves constructor
minimum closure. Its key equality branch reduces constructed-key comparisons
to strictly smaller public argument comparisons. These are dependencies of B8;
the global expanded-frame observation induction remains open.

## Claims and premises

The frame retains the original election key and two honest ballots, with one
handle for each published partial and result. Under `ExpandedResultsNumeric`,
`expanded_projection_pk_origin` proves that a key-valued projection chain is
exactly the original election-key handle. Honest ballot fields contain no key
values; partial slots are opaque partial constructors; numeric result slots
cannot be keys or pairs. Actual accepted public elections discharge the numeric
premise using `accepted_expanded_results_numeric`.

`Frame.minimum_public_key_form_of_origins` extracts the structural argument
previously embedded in the initial-frame proof. It requires pair origins,
no successful whole-minimum decryption, and a classified key-valued selector
chain. Both the original initial-frame theorem and
`expanded_minimum_public_key_form` now instantiate this same argument. The
expanded instance discharges these premises using the actual published frame.
Its conclusion is `ExpandedPublicKeyRecipeForm`: the retained election-key
handle or an explicit `pk` constructor. The accepted-election wrapper has no
unproved origin or certificate premise.

With public submissions and the full restricted-name policy,
`expanded_constructed_key_not_election_key` uses published-frame name
non-deducibility to exclude a public argument equal to the election secret.
It needs neither freshness nor accepted submissions. With numeric results,
`expanded_minimum_election_key_handle` gives the unique minimum recipe for the
election key, and `expanded_minimum_pk_of_child` proves that any minimum public
argument produces a minimum constructed key. The latter compares with an
arbitrary minimum competitor, classifies its origin, excludes the borrowed
case and uses key injectivity in the constructed case.

`expanded_key_form_equality_swap` covers all four form pairs. Two retained
handles are equal. Both mixed comparisons are false by name non-deducibility.
Two constructors compare their arguments under the strict smaller-observation
bound. `expanded_minimum_public_key_equality_swap` derives the source forms;
`accepted_expanded_minimum_public_key_equality_swap` also discharges numeric
results. **The smaller-observation premise remains explicit.** Its general
instance belongs to the still-open expanded-frame induction.

## Independent controls

Eight checked statements in `ExpandedKeySPOT.lean` cover:

- The retained election key is minimum and its minimum recipe is unique.
- A key constructed from a published partial has minimum size two and differs
  from the election key.
- A nested partial constructor using partial and result handles also supports
  minimum key construction and cannot alias the election key.
- A projection of an explicit pair returns the election key while violating
  both minimum size and the claimed raw key syntax.
- Removing the election secret from the restricted policy makes the explicit
  constructed key equal its handle. The public size-one secret argument then
  fails to produce a minimum key constructor.
- Projections from new partial and numeric result handles cannot return keys.
- The accepted equality interface is inhabited by distinct constructed keys
  in a diagonal election; equality is not an always-true conclusion.
- Structured-key E5 succeeds with a key-valued payload, but its decryption
  wrapper is nonminimum and does not have the classified raw syntax.

The executable gate detects both omitted-minimum and omitted-secret-policy
mutations at input zero, seed 1, with zero shrinks. Seeds 1, 7 and 42 each pass
500 cases at size 40 with `gaveUp=0`; 2048 deterministic inputs also pass.
The fixtures use both candidates and assignments, and constructed keys over
partial/result handles, nested partials, pairs, keys and compositions. This is
bounded executable evidence using `normalizeRaw`, which is not a complete
full-E decision procedure. The general proofs use full E.

## Evidence and remaining work

The pre-proof gate is recorded in
`tmp/variable-overlap/expanded-key-gate.log`. The origin, transport and eight-control targeted
builds pass (926, 927 and 1026 jobs respectively). Full `lake build` passes
3642 jobs. Its audit reports 1926 nonempty standard-only axiom dependencies
and 20 axiom-free declarations. The claim checker covers 960 public theorem
entries and 51 current-status documents. Nineteen new theorem audits include
the eight controls; one definition check is added. Integrated log:
`tmp/variable-overlap/expanded-key-full-build.log`. The new
artifacts are `PublicKeyMinimumTools.lean`, `ExpandedPublicKeyOrigins.lean`,
`ExpandedPublicKeyTransport.lean`, `ExpandedKeySPOT.lean` and
`ExpandedKeyExperiments.lean`. The original `minimum_public_key_form` keeps its
public type while reusing the extracted structural proof.

The source model's equations and public observations are unchanged. This work
does not supply the other expanded-value equality branches, their global
shared-minimum/smaller-observation induction, historical process matching, or
the full symbolic secrecy theorem. The maintained
[blueprint](helios-proof-blueprint.md) remains at B8, seven of ten completed
milestones (70% unweighted milestone coverage).
