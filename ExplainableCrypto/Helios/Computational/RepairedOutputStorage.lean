import ExplainableCrypto.Helios.Computational.RepairedFiniteProgrammed

/-! Retained submission output shapes, derived through actual source support.
Rejection preserves the board; arbitrary attacker ballots have fixed arity. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type}

/-- Both ciphertext pairs and all three proof commitment pairs, in ballot order. -/
def ballotGroupRecord (b : Ballot F G 2) : List G :=
  [b.ciphertext 0 |>.1,b.ciphertext 0 |>.2,b.ciphertext 1 |>.1,b.ciphertext 1 |>.2,
   (b.proof 0).zero.a,(b.proof 0).zero.b,(b.proof 0).one.a,(b.proof 0).one.b,
   (b.proof 1).zero.a,(b.proof 1).zero.b,(b.proof 1).one.a,(b.proof 1).one.b,
   b.overall.zero.a,b.overall.zero.b,b.overall.one.a,b.overall.one.b]

def ballotScalarRecord (b : Ballot F G 2) : List F :=
  [(b.proof 0).zero.challenge,(b.proof 0).zero.response,
   (b.proof 0).one.challenge,(b.proof 0).one.response,
   (b.proof 1).zero.challenge,(b.proof 1).zero.response,
   (b.proof 1).one.challenge,(b.proof 1).one.response,
   b.overall.zero.challenge,b.overall.zero.response,b.overall.one.challenge,b.overall.one.response]

theorem ballotGroupRecord_length (b : Ballot F G 2) : (ballotGroupRecord b).length = 16 := rfl

theorem ballotScalarRecord_length (b : Ballot F G 2) : (ballotScalarRecord b).length = 12 := rfl

/-- Project all retained ballots, including both boards and the submitted ballot.
Decisions and voter identifiers remain in the original output object. -/
def submissionGroupRecord (out : RepairedSubmissionResult F G) : List G :=
  out.honest.2.flatMap (fun e => ballotGroupRecord e.ballot) ++ ballotGroupRecord out.ballot ++
    out.board.flatMap (fun e => ballotGroupRecord e.ballot)

def submissionScalarRecord (out : RepairedSubmissionResult F G) : List F :=
  out.honest.2.flatMap (fun e => ballotScalarRecord e.ballot) ++ ballotScalarRecord out.ballot ++
    out.board.flatMap (fun e => ballotScalarRecord e.ballot)

private theorem board_lengths (xs : List (BoardEntry F G)) :
    (xs.flatMap (fun e => ballotGroupRecord e.ballot)).length = 16*xs.length ∧
    (xs.flatMap (fun e => ballotScalarRecord e.ballot)).length = 12*xs.length := by
  induction xs with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,ballotGroupRecord_length,
      ballotScalarRecord_length,ih.1,ih.2,List.length_cons]
    constructor <;> omega

/-- Exact group/scalar cell counts in the retained-output projections. -/
theorem submissionRecord_lengths (out : RepairedSubmissionResult F G) :
    (submissionGroupRecord out).length = 16*(out.honest.2.length+1+out.board.length) ∧
    (submissionScalarRecord out).length = 12*(out.honest.2.length+1+out.board.length) := by
  simp only [submissionGroupRecord,submissionScalarRecord,List.length_append,
    ballotGroupRecord_length,ballotScalarRecord_length,(board_lengths _).1,(board_lengths _).2]
  constructor <;> omega

variable [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

private theorem submit_length (g pk : G) (voter : Fin 3)
    (board : List (BoardEntry F G)) (b : Ballot F G 2)
    (out : Decision × List (BoardEntry F G))
    (ho : out ∈ support (repairedSubmitOracle g pk voter board b)) :
    out.2.length ≤ board.length+1 := by
  simp only [repairedSubmitOracle,mem_support_bind_iff] at ho
  obtain ⟨valid,_,ho⟩ := ho
  split at ho
  · split at ho
    · simp only [mem_support_pure_iff] at ho
      subst out
      simp
    · simp only [mem_support_pure_iff] at ho
      subst out
      exact Nat.le_add_right _ _
  · simp only [mem_support_pure_iff] at ho
    subst out
    exact Nat.le_add_right _ _

variable [SampleableType F] [Fintype F]

omit [SampleableType F] in
private theorem prefix_length (g pk : G) (vote : Bool) (out : HonestPrefixView F G)
    (ho : out ∈ support (repairedCastHonestPairOracle g pk vote)) : out.2.length ≤ 2 := by
  simp only [repairedCastHonestPairOracle,mem_support_bind_iff,mem_support_pure_iff] at ho
  obtain ⟨alice,_,first,hfirst,bob,_,second,hsecond,rfl⟩ := ho
  have h1 := submit_length g pk 0 [] alice first
    (mem_support_of_mem_support_liftComp _ _ _ hfirst)
  have h2 := submit_length g pk 1 first.2 bob second
    (mem_support_of_mem_support_liftComp _ _ _ hsecond)
  change second.2.length ≤ 2
  simp only [List.length_nil] at h1
  omega

omit [SampleableType F] in
/-- Actual source support retains at most two prefix entries and three final
entries, including every proof/reuse rejection and arbitrary attacker ballots. -/
theorem repairedSubmission_output_board_lengths (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2))
    (out : RepairedSubmissionResult F G)
    (ho : out ∈ support (repairedSubmissionOracle g pk vote attacker)) :
    out.honest.2.length ≤ 2 ∧ out.board.length ≤ 3 := by
  simp only [repairedSubmissionOracle,mem_support_bind_iff,mem_support_pure_iff] at ho
  obtain ⟨honest,hh,ballot,_,cast,hcast,rfl⟩ := ho
  have hp := prefix_length g pk vote honest hh
  have hc := submit_length g pk 2 honest.2 ballot cast
    (mem_support_of_mem_support_liftComp _ _ _ hcast)
  exact ⟨hp,by dsimp; omega⟩

/-- The output-shape bound also holds in the complete probabilistic execution
with both finite caches; source support is derived through both interpreters. -/
theorem repairedSubmissionFinite_output_board_lengths (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2))
    (out : (RepairedSubmissionResult F G × BallotFiniteProgrammedState F G) ×
      BallotFiniteCache F G)
    (ho : out ∈ support (runBallotFiniteProgrammed g pk
      (repairedSubmissionOracle g pk vote attacker))) :
    out.1.1.honest.2.length ≤ 2 ∧ out.1.1.board.length ≤ 3 := by
  apply repairedSubmission_output_board_lengths g pk vote attacker out.1.1
  apply support_simulateQ_run'_subset (ballotFiniteProgrammedImpl g pk) _ .empty
  rw [StateT.run'_eq,support_map]
  apply Set.mem_image_of_mem Prod.fst
  apply support_simulateQ_run'_subset ballotFiniteCacheImpl _ ∅
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst ho

/-- The complete probabilistic source retains at most six ballot records,
including both boards. Scalar/group widths and machine representations are separate. -/
theorem repairedSubmissionFinite_output_cells_le (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2))
    (out : (RepairedSubmissionResult F G × BallotFiniteProgrammedState F G) ×
      BallotFiniteCache F G)
    (ho : out ∈ support (runBallotFiniteProgrammed g pk
      (repairedSubmissionOracle g pk vote attacker))) :
    (submissionGroupRecord out.1.1).length ≤ 96 ∧
      (submissionScalarRecord out.1.1).length ≤ 72 := by
  have h := repairedSubmissionFinite_output_board_lengths g pk vote attacker out ho
  have hr := submissionRecord_lengths out.1.1
  constructor <;> omega

#print axioms ballotGroupRecord_length
#print axioms ballotScalarRecord_length
#print axioms submissionRecord_lengths
#print axioms repairedSubmissionFinite_output_cells_le
#print axioms repairedSubmission_output_board_lengths
#print axioms repairedSubmissionFinite_output_board_lengths
end ExplainableCrypto.Helios.Computational
