import ExplainableCrypto.Helios.Computational.ReplayBitsCodec
import ExplainableCrypto.Helios.Computational.RepairedFiniteReplay

/-! Save actual entropy as bits and resume the existing finite joint replay.
Frames are collected during execution; a complete typed tape is not first
collected and then serialized. OracleComp continuation costs remain open. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
open PFunctor.FreeM
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
variable {q : Nat} {A : Type}

/-- Accumulate a frame count and encoded frames while performing each query. -/
def replayBitsCollectFrames : PFunctor.FreeM (FiatShamir.Fork.wrappedSpec (ZMod q)).toPFunctor A →
    PFunctor.FreeM (FiatShamir.Fork.wrappedSpec (ZMod q)).toPFunctor (Nat × List Bool)
  | .pure _ => .pure (0,[])
  | .liftBind t next => .liftBind t fun a => PFunctor.FreeM.map
      (fun out => (out.1+1,replayEventFrame ⟨t,a⟩ ++ out.2)) (replayBitsCollectFrames (next a))

/-- The direct encoded collector preserves the original query tree exactly. -/
theorem replayBitsCollectFrames_eq
    (oa : PFunctor.FreeM (FiatShamir.Fork.wrappedSpec (ZMod q)).toPFunctor A) :
    replayBitsCollectFrames oa = PFunctor.FreeM.map
      (fun tape : ReplayTape q => (tape.length,replayFramesEncode tape)) (ballotReplayCollectTape oa) := by
  induction oa with
  | pure x => rfl
  | lift_bind t next ih =>
    change replayBitsCollectFrames (.liftBind t next) = PFunctor.FreeM.map
      (fun tape : ReplayTape q => (tape.length,replayFramesEncode tape))
        (ballotReplayCollectTape (.liftBind t next))
    simp only [replayBitsCollectFrames,ballotReplayCollectTape,PFunctor.FreeM.map]
    apply congrArg (PFunctor.FreeM.liftBind t)
    funext a
    rw [ih a,← PFunctor.FreeM.comp_map,← PFunctor.FreeM.comp_map]
    rfl

def replayBitsCollect (oa : OracleComp (FiatShamir.Fork.wrappedSpec (ZMod q)) A) :
    OracleComp (FiatShamir.Fork.wrappedSpec (ZMod q)) (List Bool) :=
  PFunctor.FreeM.map (fun out => uniformNatEncode out.1 ++ out.2) (replayBitsCollectFrames oa)

theorem replayBitsCollect_eq (oa : OracleComp (FiatShamir.Fork.wrappedSpec (ZMod q)) A) :
    replayBitsCollect oa = replayTapeEncode <$>
      (ballotReplayCollectTape oa : OracleComp (FiatShamir.Fork.wrappedSpec (ZMod q)) (ReplayTape q)) := by
  unfold replayBitsCollect
  rw [replayBitsCollectFrames_eq,← PFunctor.FreeM.comp_map]
  rfl

variable {G : Type} [Fact q.Prime] [AddCommGroup G] [Module (ZMod q) G]
  [DecidableEq G] [SampleableType (ZMod q)]

def ballotJointReplayAtBits (oa : BallotOracleComp (ZMod q) G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 (ZMod q) G)
    (n : Nat) (word : List Bool) : OracleComp (FiatShamir.Fork.wrappedSpec (ZMod q))
      (Option (A × (Option (Fin 2) → BallotWitness (ZMod q)))) :=
  match replayTapeDecode q word with
  | none => pure none
  | some tape => ballotFiniteJointReplayAtTape oa select n tape

def ballotJointReplayBits (oa : BallotOracleComp (ZMod q) G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 (ZMod q) G) (n : Nat) :
    OracleComp (FiatShamir.Fork.wrappedSpec (ZMod q))
      (Option (A × (Option (Fin 2) → BallotWitness (ZMod q)))) := do
  let word ← replayBitsCollect (ballotFiniteReplaySourceRun oa)
  ballotJointReplayAtBits oa select n word

omit [SampleableType (ZMod q)] in
/-- The original source, all three residual attempts and every failure retain
exactly the existing algorithm. There is no caller codec-validity premise. -/
theorem ballotJointReplayBits_eq (oa : BallotOracleComp (ZMod q) G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 (ZMod q) G) (n : Nat) :
    ballotJointReplayBits oa select n = ballotFiniteJointReplay oa select n := by
  unfold ballotJointReplayBits ballotFiniteJointReplay
  rw [replayBitsCollect_eq,bind_map_left]
  apply bind_congr
  intro tape
  simp [ballotJointReplayAtBits,replayTapeDecode_encode]

noncomputable def repairedSubmissionBits_extract (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (n : Nat) : OracleComp (FiatShamir.Fork.wrappedSpec (ZMod q))
      (Option (RepairedSubmissionResult (ZMod q) G × (Option (Fin 2) → BallotWitness (ZMod q)))) :=
  ballotJointReplayBits (repairedSubmissionFiniteSourceOracle g pk vote attacker)
    (repairedSubmissionSelect g pk) (n+15)

attribute [local irreducible] repairedSubmissionFiniteSourceOracle

/-- The actual historical prime-scalar extractor now saves bits, preserving its
complete existing output, witness, randomness and rejection semantics. -/
theorem repairedSubmissionBits_extract_eq (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (n : Nat) : repairedSubmissionBits_extract g pk vote attacker n =
      repairedSubmission_joint_extract g pk vote attacker n := by
  unfold repairedSubmissionBits_extract
  rw [ballotJointReplayBits_eq]
  exact repairedSubmissionFinite_extract_eq g pk vote attacker n

#print axioms replayBitsCollectFrames_eq
#print axioms replayBitsCollect_eq
#print axioms ballotJointReplayBits_eq
#print axioms repairedSubmissionBits_extract_eq
end ExplainableCrypto.Helios.Computational
