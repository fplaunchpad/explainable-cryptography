import ExplainableCrypto.Helios.Computational.PrimeSimOneTail
import ExplainableCrypto.Helios.Computational.PrimeSimOneFirstMachineSource
import ExplainableCrypto.Helios.Computational.PrimeSimOneSecondMachineSource

namespace ExplainableCrypto.Helios.Computational.PrimeSimOneTail
open OracleComp BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
attribute [local irreducible] BitOracleMachine.run
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
  (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
  (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q))

def sourceResult : Config :=
  BitOracleReturnLink.embed secondLabel none
    (PrimeSimOneSecondMachine.sourceResult slack g pk vote saved out)

/-- These are complete reached-state return identities, including new blank
ports and every earlier scalar, ciphertext, commitment and private word. -/
theorem beta_return :
    BitOracleReturnLink.embed betaLabel (some (firstLabel 0))
      (BitOracleStackFrame.embed betaLayout
        (PrimeAdjustedBetaMachine.sourceResult slack g pk vote saved out) (fun _ => [])) =
    BitOracleReturnLink.embed firstLabel (some (secondLabel 0))
      (BitOracleStackFrame.embed firstLayout
        (PrimeSimOneFirstMachine.start
          (PrimeAdjustedBetaMachine.sourceResult slack g pk vote saved out).stk) (fun _ => [])) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

theorem first_return :
    BitOracleReturnLink.embed firstLabel (some (secondLabel 0))
      (BitOracleStackFrame.embed firstLayout
        (PrimeSimOneFirstMachine.sourceResult slack g pk vote saved out) (fun _ => [])) =
    BitOracleReturnLink.embed secondLabel none
      (PrimeSimOneSecondMachine.start
        (PrimeSimOneFirstMachine.sourceResult slack g pk vote saved out).stk) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

private theorem second_charged :
    ∃ charge ≤ PrimeSimCommitMachine.cost p q,
      BitOracleMachine.run code (PrimeSimCommitMachine.clock p q)
        (BitOracleReturnLink.embed secondLabel none
          (PrimeSimOneSecondMachine.start
            (PrimeSimOneFirstMachine.sourceResult slack g pk vote saved out).stk)) =
      pure (sourceResult slack g pk vote saved out,charge) := by
  obtain ⟨charge,hc,he⟩ := PrimeSimOneSecondMachine.charged_source slack g pk vote saved out
  simp only [PrimeSimOneSecondMachine.clock] at he
  rw [BitOracleReturnLink.rename_run _ _ _ second_code,he,map_pure]
  exact ⟨charge,hc,rfl⟩

private theorem first_pair_charged :
    ∃ charge ≤ 2*PrimeSimCommitMachine.cost p q,
      BitOracleMachine.run code (PrimeSimCommitMachine.clock p q+PrimeSimCommitMachine.clock p q)
        (BitOracleReturnLink.embed firstLabel (some (secondLabel 0))
          (BitOracleStackFrame.embed firstLayout
            (PrimeSimOneFirstMachine.start
              (PrimeAdjustedBetaMachine.sourceResult slack g pk vote saved out).stk) (fun _ => []))) =
      pure (sourceResult slack g pk vote saved out,charge) := by
  obtain ⟨lastCost,hlc,hl⟩ := second_charged slack g pk vote saved out
  obtain ⟨firstCost,hfc,hf⟩ := PrimeSimOneFirstMachine.charged_source slack g pk vote saved out
  simp only [PrimeSimOneFirstMachine.clock] at hf
  have hframe := BitOracleStackFrame.run firstLayout PrimeSimOneFirstMachine.code
    (PrimeSimCommitMachine.clock p q)
    (PrimeSimOneFirstMachine.start
      (PrimeAdjustedBetaMachine.sourceResult slack g pk vote saved out).stk) (fun _ => [])
  rw [hf,map_pure] at hframe
  let initial := BitOracleStackFrame.embed firstLayout
    (PrimeSimOneFirstMachine.start
      (PrimeAdjustedBetaMachine.sourceResult slack g pk vote saved out).stk) (fun _ => [])
  have hh : ∀ v ∈ support (BitOracleMachine.run firstCode (PrimeSimCommitMachine.clock p q) initial),
      v.1.l = none := by
    dsimp only [firstCode,betaCode,initial]
    rw [hframe]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    rfl
  have ht : ∀ v ∈ support (BitOracleMachine.run firstCode (PrimeSimCommitMachine.clock p q) initial),
      ∀ last ∈ support (BitOracleMachine.run code (PrimeSimCommitMachine.clock p q)
        (BitOracleReturnLink.embed firstLabel (some (secondLabel 0)) v.1)), last.1.l = none := by
    dsimp only [firstCode,betaCode,initial]
    rw [hframe]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    rw [first_return,hl]
    intro last hlast
    obtain rfl := eq_of_mem_support_pure _ hlast
    rfl
  have h := BitOracleReturnLink.run firstCode code firstLabel (secondLabel 0) first_code
    (PrimeSimCommitMachine.clock p q) (PrimeSimCommitMachine.clock p q) initial hh ht
  dsimp only [firstCode,initial] at h
  rw [hframe,pure_bind,first_return,hl,pure_bind] at h
  exact ⟨firstCost+lastCost,by change firstCost ≤ PrimeSimCommitMachine.cost p q at hfc; omega,h⟩

/-- The actual adjusted-base and both one-branch coordinates execute in one
finite tail. Its full state and total charge follow from reached source values. -/
theorem charged_source :
    ∃ charge ≤ cost p q,
      BitOracleMachine.run code (clock p q)
        (start (PrimeSimDifferenceMachine.sourceResult slack g pk vote saved out).stk) =
      pure (sourceResult slack g pk vote saved out,charge) := by
  obtain ⟨lastCost,hlc,hl⟩ := first_pair_charged slack g pk vote saved out
  obtain ⟨betaCost,hbc,hb⟩ := PrimeAdjustedBetaMachine.charged_source slack g pk vote saved out
  have hframe := BitOracleStackFrame.run betaLayout PrimeAdjustedBetaMachine.code
    (PrimeAdjustedBetaMachine.clock p q)
    (PrimeAdjustedBetaMachine.start
      (PrimeSimDifferenceMachine.sourceResult slack g pk vote saved out).stk) (fun _ => [])
  rw [hb,map_pure] at hframe
  let initial := BitOracleStackFrame.embed betaLayout
    (PrimeAdjustedBetaMachine.start
      (PrimeSimDifferenceMachine.sourceResult slack g pk vote saved out).stk) (fun _ => [])
  have hh : ∀ v ∈ support (BitOracleMachine.run betaCode (PrimeAdjustedBetaMachine.clock p q) initial),
      v.1.l = none := by
    dsimp only [firstCode,betaCode,initial]
    rw [hframe]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    rfl
  have ht : ∀ v ∈ support (BitOracleMachine.run betaCode (PrimeAdjustedBetaMachine.clock p q) initial),
      ∀ last ∈ support (BitOracleMachine.run code
        (PrimeSimCommitMachine.clock p q+PrimeSimCommitMachine.clock p q)
        (BitOracleReturnLink.embed betaLabel (some (firstLabel 0)) v.1)), last.1.l = none := by
    dsimp only [firstCode,betaCode,initial]
    rw [hframe]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    rw [beta_return,hl]
    intro last hlast
    obtain rfl := eq_of_mem_support_pure _ hlast
    rfl
  have h := BitOracleReturnLink.run betaCode code betaLabel (firstLabel 0) beta_code
    (PrimeAdjustedBetaMachine.clock p q)
    (PrimeSimCommitMachine.clock p q+PrimeSimCommitMachine.clock p q) initial hh ht
  dsimp only [betaCode,initial] at h
  rw [hframe,pure_bind,beta_return,hl,pure_bind] at h
  refine ⟨betaCost+lastCost,Nat.add_le_add hbc hlc,?_⟩
  simpa only [clock,start,two_mul] using h

theorem source :
    Prod.fst <$> BitOracleMachine.run code (clock p q)
      (start (PrimeSimDifferenceMachine.sourceResult slack g pk vote saved out).stk) =
    pure (sourceResult slack g pk vote saved out) := by
  obtain ⟨charge,_,he⟩ := charged_source slack g pk vote saved out
  rw [he,map_pure]

#print axioms beta_return
#print axioms first_return
#print axioms charged_source
#print axioms source
end ExplainableCrypto.Helios.Computational.PrimeSimOneTail
