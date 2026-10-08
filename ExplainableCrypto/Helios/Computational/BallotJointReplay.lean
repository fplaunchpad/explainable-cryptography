import ExplainableCrypto.Helios.Computational.BallotReplaySource

/-! Three conditional replays share one original source execution. Success is
checked against that original source's three selected statements and full proofs.
A quantitative joint success bound is a separate obligation. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G A : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F]

def ballotJointWitnesses (w0 w1 wa : BallotWitness F) : Option (Fin 2) → BallotWitness F
  | none => wa
  | some i => if i = 0 then w0 else w1

def ballotJointReplayAtPath (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun oa)) := do
  let w0 ← ballotReplaySourceAttempt oa (select (some 0)) n path
  let w1 ← ballotReplaySourceAttempt oa (select (some 1)) n path
  let wa ← ballotReplaySourceAttempt oa (select none) n path
  pure (do return ballotJointWitnesses (← w0) (← w1) (← wa))

def ballotJointReplay (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat) := do
  let path ← replayFirstPath (ballotReplaySourceRun oa)
  Option.map (fun w => ((PFunctor.FreeM.output _ path).1,w)) <$>
    ballotJointReplayAtPath oa select n path

section Probability
variable [Fintype F]
local instance jointReplayInhabited : Inhabited F := ⟨0⟩
noncomputable local instance jointReplayUniform : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

omit [Fintype F] in
/-- Every joint success consists of three supported conditional attempts at
this same path. There is no assumed agreement between separate source runs. -/
theorem ballotJointReplayAtPath_supported (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun oa))
    (w : Option (Fin 2) → BallotWitness F)
    (hw : some w ∈ support (ballotJointReplayAtPath oa select n path)) :
    ∀ i, some (w i) ∈ support (ballotReplaySourceAttempt oa (select i) n path) := by
  simp only [ballotJointReplayAtPath,mem_support_bind_iff,mem_support_pure_iff] at hw
  obtain ⟨w0,h0,w1,h1,wa,ha,he⟩ := hw
  cases w0 with
  | none => simp at he
  | some w0 =>
    cases w1 with
    | none => simp at he
    | some w1 =>
      cases wa with
      | none => simp at he
      | some wa =>
        have he' : ballotJointWitnesses w0 w1 wa = w := Option.some.inj he.symm
        subst w
        intro i
        cases i with
        | none => exact ha
        | some i => fin_cases i <;> simpa [ballotJointWitnesses] using (by assumption)

/-- Actual joint output: all three witnesses and original full-proof validity
belong to the retained source result, which has a supported original execution. -/
theorem ballotJointReplay_valid (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat)
    (result : A) (w : Option (Fin 2) → BallotWitness F)
    (hw : some (result,w) ∈ support (ballotJointReplay oa select n)) :
    (∀ i, (select i result).1.Witnesses (w i) ∧ ∃ c : F,
      (select i result).2.Valid (fun _ => c) (select i result).1.generator
        (select i result).1.publicKey (select i result).1.ciphertext) ∧
      ∃ cache, (result,cache) ∈ support (runBallotOracle oa ∅) := by
  rw [ballotJointReplay,mem_support_bind_iff] at hw
  obtain ⟨path,_,hw⟩ := hw
  rw [support_map] at hw
  obtain ⟨ow,ho,he⟩ := hw
  cases ow with
  | none => simp at he
  | some ws =>
    have he' : ((PFunctor.FreeM.output _ path).1,ws) = (result,w) := Option.some.inj he
    obtain ⟨hr,rfl⟩ := Prod.mk.inj he'
    constructor
    · intro i
      have hv := ballotReplaySourceAttempt_valid oa (select i) n path (ws i)
        (ballotJointReplayAtPath_supported oa select n path ws ho i)
      simpa only [hr] using hv
    · simpa only [hr] using ballotReplaySourcePath_mem oa path
end Probability

#print axioms ballotJointReplayAtPath_supported
#print axioms ballotJointReplay_valid
end ExplainableCrypto.Helios.Computational
