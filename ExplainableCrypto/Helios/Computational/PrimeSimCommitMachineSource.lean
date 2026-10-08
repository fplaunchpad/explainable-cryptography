import ExplainableCrypto.Helios.Computational.PrimeSimCommitMachineRun
import ExplainableCrypto.Helios.Computational.PrimeSimCommitSource

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
open OracleComp BitOracleMachine

/-- Complete first-commitment result from the actual typed prior source state.
Only coordinate port three changes; all original words and appended cleanup
remain explicit in the existing full-state result constructor. -/
def sourceResult {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) : Config :=
  result
    (primeGroupCoordinate (ballotSimCommit (honestProofStatement g pk (vote,out.1.1))
      out.2.1 (out.2.2.1,out.2.2.2.1,out.2.2.2.2)).1.1).val.bits
    (PrimeHonestTranscriptCaller.sourceResult slack g pk vote saved out).stk

private theorem answer_source {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    answer p q (primeGroupCoordinate g).val
      (primeGroupCoordinate (encryptWith g pk out.1.1 (voteScalar vote)).1).val
      out.2.2.1.val out.2.2.2.1.val =
    (primeGroupCoordinate (ballotSimCommit (honestProofStatement g pk (vote,out.1.1))
      out.2.1 (out.2.2.1,out.2.2.2.1,out.2.2.2.2)).1.1).val := by
  simpa only [answer,honestProofStatement] using
    (PrimeSimCommitSource.first_coordinate_value (honestProofStatement g pk (vote,out.1.1))
      out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2).symm

/-- The actual source state supplies every operand, bound and private frame.
This executes the first simulated commitment coordinate, not the rest of the
proof construction or a secrecy property. -/
theorem source {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    tick^[clock p q]
      (start (PrimeHonestTranscriptCaller.sourceResult slack g pk vote saved out).stk) =
      sourceResult slack g pk vote saved out := by
  let old := PrimeHonestTranscriptCaller.sourceResult slack g pk vote saved out
  have h := padded_run p q (primeGroupCoordinate g).val
    (primeGroupCoordinate (encryptWith g pk out.1.1 (voteScalar vote)).1).val
    out.2.2.1.val out.2.2.2.1.val (Fact.out : p.Prime).two_le
    (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
    ![old.stk 0,old.stk 7,old.stk 10,old.stk 13,old.stk 14,old.stk 15,
      old.stk 18,old.stk 19,old.stk 20,old.stk 21,old.stk 22]
  dsimp only [old] at h
  rw [inputWords_source,answer_source] at h
  exact h

/-- The complete source result and charge follow from the actual numeric run.
The preceding raw source supplies the words; no reconstruction or runtime
certificate is an argument. -/
theorem charged_source {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    ∃ charge ≤ cost p q,
      BitOracleMachine.run code (clock p q)
        (start (PrimeHonestTranscriptCaller.sourceResult slack g pk vote saved out).stk) =
      pure (sourceResult slack g pk vote saved out,charge) := by
  let old := PrimeHonestTranscriptCaller.sourceResult slack g pk vote saved out
  obtain ⟨charge,hc,he⟩ := charged p q (primeGroupCoordinate g).val
    (primeGroupCoordinate (encryptWith g pk out.1.1 (voteScalar vote)).1).val
    out.2.2.1.val out.2.2.2.1.val (Fact.out : p.Prime).two_le
    (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
    ![old.stk 0,old.stk 7,old.stk 10,old.stk 13,old.stk 14,old.stk 15,
      old.stk 18,old.stk 19,old.stk 20,old.stk 21,old.stk 22]
  dsimp only [old] at he
  rw [inputWords_source,answer_source] at he
  exact ⟨charge,hc,he⟩

#print axioms source
#print axioms charged_source
end ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
