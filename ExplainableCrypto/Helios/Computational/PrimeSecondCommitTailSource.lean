import ExplainableCrypto.Helios.Computational.PrimeSecondCommitTail
import ExplainableCrypto.Helios.Computational.PrimeSecondOneSecondMachineSource

namespace ExplainableCrypto.Helios.Computational.PrimeSecondCommitTail
open OracleComp OracleSpec BitOracleMachine
open PrimeProgramProofSource (State Cache Draws)
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
  (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
  (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
  (cs : ZMod q × ZMod q × ZMod q × ZMod q)
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
attribute [local irreducible] BitOracleMachine.run

def sourceResult : Config :=
  BitOracleReturnLink.embed secondLabel none
    (PrimeSecondOneSecondMachine.sourceResult slack g pk vote s live out cs)

/-- Complete preservation of the reached first-coordinate state, including p0,
both nonce prefixes, fresh scalars, the first p1 coordinate and saved state. -/
theorem source_retained (k : Fin 65) :
    (sourceResult slack g pk vote s live out cs).stk ⟨k.val,by omega⟩ =
      (PrimeSecondCommitMachine.sourceResult slack g pk vote s live out cs).stk k := by
  calc
    _ = (PrimeSecondOneFirstMachine.sourceResult slack g pk vote s live out cs).stk
        ⟨k.val,by omega⟩ :=
      PrimeSecondOneSecondMachine.source_retained slack g pk vote s live out cs ⟨k.val,by omega⟩
    _ = (PrimeSecondAdjustedMachine.sourceResult slack g pk vote s live out cs).stk
        ⟨k.val,by omega⟩ :=
      PrimeSecondOneFirstMachine.source_retained slack g pk vote s live out cs ⟨k.val,by omega⟩
    _ = (PrimeSecondDifferenceMachine.sourceResult slack g pk vote s live out cs).stk
        ⟨k.val,by omega⟩ :=
      PrimeSecondAdjustedMachine.source_retained slack g pk vote s live out cs ⟨k.val,by omega⟩
    _ = (PrimeSecondCommitBMachine.sourceResult slack g pk vote s live out cs).stk
        ⟨k.val,by omega⟩ :=
      PrimeSecondDifferenceMachine.source_retained slack g pk vote s live out cs ⟨k.val,by omega⟩
    _ = _ := PrimeSecondCommitBMachine.source_retained slack g pk vote s live out cs k

/-- All four fields belong to the original p1 simulator commitment, with its
fresh transcript and retained second nonce. -/
theorem source_commitments :
    let cfg := sourceResult slack g pk vote s live out cs
    let com := PrimeSecondCommitSource.commitment g pk out cs
    cfg.stk 60 = (primeGroupCoordinate com.1.1).val.bits ∧
    cfg.stk 65 = (primeGroupCoordinate com.1.2).val.bits ∧
    cfg.stk 68 = (primeGroupCoordinate com.2.1).val.bits ∧
    cfg.stk 69 = (primeGroupCoordinate com.2.2).val.bits := ⟨rfl,rfl,rfl,rfl⟩

/-- The canonical challenge difference and adjusted ciphertext are resident
source values, available to the next key/proof construction. -/
theorem source_preparation :
    let cfg := sourceResult slack g pk vote s live out cs
    cfg.stk 66 = scalarEncode (cs.1-cs.2.1) ∧
    cfg.stk 67 = (primeGroupCoordinate
      ((PrimeSecondCommitSource.statement g pk out).ciphertext.2-g)).val.bits := ⟨rfl,rfl⟩

private theorem b_source_return :
    BitOracleReturnLink.embed bLabel (some (differenceLabel 0))
      (BitOracleStackFrame.embed bLayout (PrimeSecondCommitBMachine.sourceResult slack g pk vote s live out cs) (fun _ => [])) =
    (BitOracleReturnLink.embed differenceLabel (some (adjustedLabel 0)) (BitOracleStackFrame.embed differenceLayout (PrimeSecondDifferenceMachine.start (PrimeSecondCommitBMachine.sourceResult slack g pk vote s live out cs).stk) (fun _ => []))) := b_return (PrimeSecondCommitBMachine.sourceResult slack g pk vote s live out cs).stk

private theorem difference_source_return :
    BitOracleReturnLink.embed differenceLabel (some (adjustedLabel 0))
      (BitOracleStackFrame.embed differenceLayout (PrimeSecondDifferenceMachine.sourceResult slack g pk vote s live out cs) (fun _ => [])) =
    (BitOracleReturnLink.embed adjustedLabel (some (firstLabel 0)) (BitOracleStackFrame.embed adjustedLayout (PrimeSecondAdjustedMachine.start (PrimeSecondDifferenceMachine.sourceResult slack g pk vote s live out cs).stk) (fun _ => []))) := difference_return (PrimeSecondDifferenceMachine.sourceResult slack g pk vote s live out cs).stk

private theorem adjusted_source_return :
    BitOracleReturnLink.embed adjustedLabel (some (firstLabel 0))
      (BitOracleStackFrame.embed adjustedLayout (PrimeSecondAdjustedMachine.sourceResult slack g pk vote s live out cs) (fun _ => [])) =
    (BitOracleReturnLink.embed firstLabel (some (secondLabel 0)) (BitOracleStackFrame.embed firstLayout (PrimeSecondOneFirstMachine.start (PrimeSecondAdjustedMachine.sourceResult slack g pk vote s live out cs).stk) (fun _ => []))) := adjusted_return (PrimeSecondAdjustedMachine.sourceResult slack g pk vote s live out cs).stk

private theorem first_source_return :
    BitOracleReturnLink.embed firstLabel (some (secondLabel 0))
      (BitOracleStackFrame.embed firstLayout (PrimeSecondOneFirstMachine.sourceResult slack g pk vote s live out cs) (fun _ => [])) =
    (BitOracleReturnLink.embed secondLabel none (PrimeSecondOneSecondMachine.start (PrimeSecondOneFirstMachine.sourceResult slack g pk vote s live out cs).stk)) := first_return (PrimeSecondOneFirstMachine.sourceResult slack g pk vote s live out cs).stk

private theorem second_charged :
    ∃ charge ≤ PrimeSecondOneSecondMachine.cost p q,
      BitOracleMachine.run code (PrimeSecondOneSecondMachine.clock p q)
        (BitOracleReturnLink.embed secondLabel none (PrimeSecondOneSecondMachine.start (PrimeSecondOneFirstMachine.sourceResult slack g pk vote s live out cs).stk)) = pure (sourceResult slack g pk vote s live out cs,charge) := by
  obtain ⟨charge,hc,he⟩ := PrimeSecondOneSecondMachine.charged_source slack g pk vote s live out cs
  rw [BitOracleReturnLink.rename_run _ _ _ second_code,secondCode,he,map_pure]
  exact ⟨charge,hc,rfl⟩

private theorem first_charged :
    ∃ charge ≤ PrimeSecondOneFirstMachine.cost p q + (PrimeSecondOneSecondMachine.cost p q),
      BitOracleMachine.run code (PrimeSecondOneFirstMachine.clock p q + (PrimeSecondOneSecondMachine.clock p q))
        (BitOracleReturnLink.embed firstLabel (some (secondLabel 0)) (BitOracleStackFrame.embed firstLayout (PrimeSecondOneFirstMachine.start (PrimeSecondAdjustedMachine.sourceResult slack g pk vote s live out cs).stk) (fun _ => []))) = pure (sourceResult slack g pk vote s live out cs,charge) := by
  obtain ⟨lastCost,hlc,hl⟩ := second_charged slack g pk vote s live out cs
  obtain ⟨thisCost,hc,he⟩ := PrimeSecondOneFirstMachine.charged_source slack g pk vote s live out cs
  have hframe := BitOracleStackFrame.run firstLayout PrimeSecondOneFirstMachine.code
    (PrimeSecondOneFirstMachine.clock p q)
    (PrimeSecondOneFirstMachine.start (PrimeSecondAdjustedMachine.sourceResult slack g pk vote s live out cs).stk) (fun _ => [])
  rw [he,map_pure] at hframe
  let initial := BitOracleStackFrame.embed firstLayout
    (PrimeSecondOneFirstMachine.start (PrimeSecondAdjustedMachine.sourceResult slack g pk vote s live out cs).stk) (fun _ => [])
  have hh : ∀ v ∈ support (BitOracleMachine.run firstCode (PrimeSecondOneFirstMachine.clock p q) initial),
      v.1.l = none := by
    dsimp only [firstCode,initial]
    rw [hframe]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    rfl
  have ht : ∀ v ∈ support (BitOracleMachine.run firstCode (PrimeSecondOneFirstMachine.clock p q) initial),
      ∀ last ∈ support (BitOracleMachine.run code (PrimeSecondOneSecondMachine.clock p q)
        (BitOracleReturnLink.embed firstLabel (some (secondLabel 0)) v.1)), last.1.l = none := by
    dsimp only [firstCode,initial]
    rw [hframe]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    rw [first_source_return,hl]
    intro last hlast
    obtain rfl := eq_of_mem_support_pure _ hlast
    rfl
  have h := BitOracleReturnLink.run firstCode code firstLabel (secondLabel 0) first_code
    (PrimeSecondOneFirstMachine.clock p q) (PrimeSecondOneSecondMachine.clock p q) initial hh ht
  dsimp only [firstCode,initial] at h
  rw [hframe,pure_bind,first_source_return,hl,pure_bind] at h
  exact ⟨thisCost+lastCost,Nat.add_le_add hc hlc,h⟩

private theorem adjusted_charged :
    ∃ charge ≤ PrimeSecondAdjustedMachine.cost p q + (PrimeSecondOneFirstMachine.cost p q + (PrimeSecondOneSecondMachine.cost p q)),
      BitOracleMachine.run code (PrimeSecondAdjustedMachine.clock p q + (PrimeSecondOneFirstMachine.clock p q + (PrimeSecondOneSecondMachine.clock p q)))
        (BitOracleReturnLink.embed adjustedLabel (some (firstLabel 0)) (BitOracleStackFrame.embed adjustedLayout (PrimeSecondAdjustedMachine.start (PrimeSecondDifferenceMachine.sourceResult slack g pk vote s live out cs).stk) (fun _ => []))) = pure (sourceResult slack g pk vote s live out cs,charge) := by
  obtain ⟨lastCost,hlc,hl⟩ := first_charged slack g pk vote s live out cs
  obtain ⟨thisCost,hc,he⟩ := PrimeSecondAdjustedMachine.charged_source slack g pk vote s live out cs
  have hframe := BitOracleStackFrame.run adjustedLayout PrimeSecondAdjustedMachine.code
    (PrimeSecondAdjustedMachine.clock p q)
    (PrimeSecondAdjustedMachine.start (PrimeSecondDifferenceMachine.sourceResult slack g pk vote s live out cs).stk) (fun _ => [])
  rw [he,map_pure] at hframe
  let initial := BitOracleStackFrame.embed adjustedLayout
    (PrimeSecondAdjustedMachine.start (PrimeSecondDifferenceMachine.sourceResult slack g pk vote s live out cs).stk) (fun _ => [])
  have hh : ∀ v ∈ support (BitOracleMachine.run adjustedCode (PrimeSecondAdjustedMachine.clock p q) initial),
      v.1.l = none := by
    dsimp only [adjustedCode,initial]
    rw [hframe]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    rfl
  have ht : ∀ v ∈ support (BitOracleMachine.run adjustedCode (PrimeSecondAdjustedMachine.clock p q) initial),
      ∀ last ∈ support (BitOracleMachine.run code (PrimeSecondOneFirstMachine.clock p q + (PrimeSecondOneSecondMachine.clock p q))
        (BitOracleReturnLink.embed adjustedLabel (some (firstLabel 0)) v.1)), last.1.l = none := by
    dsimp only [adjustedCode,initial]
    rw [hframe]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    rw [adjusted_source_return,hl]
    intro last hlast
    obtain rfl := eq_of_mem_support_pure _ hlast
    rfl
  have h := BitOracleReturnLink.run adjustedCode code adjustedLabel (firstLabel 0) adjusted_code
    (PrimeSecondAdjustedMachine.clock p q) (PrimeSecondOneFirstMachine.clock p q + (PrimeSecondOneSecondMachine.clock p q)) initial hh ht
  dsimp only [adjustedCode,initial] at h
  rw [hframe,pure_bind,adjusted_source_return,hl,pure_bind] at h
  exact ⟨thisCost+lastCost,Nat.add_le_add hc hlc,h⟩

private theorem difference_charged :
    ∃ charge ≤ PrimeSecondDifferenceMachine.cost q + (PrimeSecondAdjustedMachine.cost p q + (PrimeSecondOneFirstMachine.cost p q + (PrimeSecondOneSecondMachine.cost p q))),
      BitOracleMachine.run code (PrimeSecondDifferenceMachine.clock q + (PrimeSecondAdjustedMachine.clock p q + (PrimeSecondOneFirstMachine.clock p q + (PrimeSecondOneSecondMachine.clock p q))))
        (BitOracleReturnLink.embed differenceLabel (some (adjustedLabel 0)) (BitOracleStackFrame.embed differenceLayout (PrimeSecondDifferenceMachine.start (PrimeSecondCommitBMachine.sourceResult slack g pk vote s live out cs).stk) (fun _ => []))) = pure (sourceResult slack g pk vote s live out cs,charge) := by
  obtain ⟨lastCost,hlc,hl⟩ := adjusted_charged slack g pk vote s live out cs
  obtain ⟨thisCost,hc,he⟩ := PrimeSecondDifferenceMachine.charged_source slack g pk vote s live out cs
  have hframe := BitOracleStackFrame.run differenceLayout PrimeSecondDifferenceMachine.code
    (PrimeSecondDifferenceMachine.clock q)
    (PrimeSecondDifferenceMachine.start (PrimeSecondCommitBMachine.sourceResult slack g pk vote s live out cs).stk) (fun _ => [])
  rw [he,map_pure] at hframe
  let initial := BitOracleStackFrame.embed differenceLayout
    (PrimeSecondDifferenceMachine.start (PrimeSecondCommitBMachine.sourceResult slack g pk vote s live out cs).stk) (fun _ => [])
  have hh : ∀ v ∈ support (BitOracleMachine.run differenceCode (PrimeSecondDifferenceMachine.clock q) initial),
      v.1.l = none := by
    dsimp only [differenceCode,initial]
    rw [hframe]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    rfl
  have ht : ∀ v ∈ support (BitOracleMachine.run differenceCode (PrimeSecondDifferenceMachine.clock q) initial),
      ∀ last ∈ support (BitOracleMachine.run code (PrimeSecondAdjustedMachine.clock p q + (PrimeSecondOneFirstMachine.clock p q + (PrimeSecondOneSecondMachine.clock p q)))
        (BitOracleReturnLink.embed differenceLabel (some (adjustedLabel 0)) v.1)), last.1.l = none := by
    dsimp only [differenceCode,initial]
    rw [hframe]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    rw [difference_source_return,hl]
    intro last hlast
    obtain rfl := eq_of_mem_support_pure _ hlast
    rfl
  have h := BitOracleReturnLink.run differenceCode code differenceLabel (adjustedLabel 0) difference_code
    (PrimeSecondDifferenceMachine.clock q) (PrimeSecondAdjustedMachine.clock p q + (PrimeSecondOneFirstMachine.clock p q + (PrimeSecondOneSecondMachine.clock p q))) initial hh ht
  dsimp only [differenceCode,initial] at h
  rw [hframe,pure_bind,difference_source_return,hl,pure_bind] at h
  exact ⟨thisCost+lastCost,Nat.add_le_add hc hlc,h⟩

theorem charged_source :
    ∃ charge ≤ cost p q,
      BitOracleMachine.run code (clock p q)
        (start (PrimeSecondCommitMachine.sourceResult slack g pk vote s live out cs).stk) = pure (sourceResult slack g pk vote s live out cs,charge) := by
  obtain ⟨lastCost,hlc,hl⟩ := difference_charged slack g pk vote s live out cs
  obtain ⟨thisCost,hc,he⟩ := PrimeSecondCommitBMachine.charged_source slack g pk vote s live out cs
  change BitOracleMachine.run PrimeSecondCommitBMachine.code (PrimeSecondCommitBMachine.clock p q)
    (PrimeSecondCommitBMachine.start (PrimeSecondCommitMachine.sourceResult slack g pk vote s live out cs).stk) =
    pure (PrimeSecondCommitBMachine.sourceResult slack g pk vote s live out cs,thisCost) at he
  have hframe := BitOracleStackFrame.run bLayout PrimeSecondCommitBMachine.code
    (PrimeSecondCommitBMachine.clock p q)
    (PrimeSecondCommitBMachine.start (PrimeSecondCommitMachine.sourceResult slack g pk vote s live out cs).stk) (fun _ => [])
  rw [he,map_pure] at hframe
  let initial := BitOracleStackFrame.embed bLayout
    (PrimeSecondCommitBMachine.start (PrimeSecondCommitMachine.sourceResult slack g pk vote s live out cs).stk) (fun _ => [])
  have hh : ∀ v ∈ support (BitOracleMachine.run bCode (PrimeSecondCommitBMachine.clock p q) initial),
      v.1.l = none := by
    dsimp only [bCode,initial]
    rw [hframe]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    rfl
  have ht : ∀ v ∈ support (BitOracleMachine.run bCode (PrimeSecondCommitBMachine.clock p q) initial),
      ∀ last ∈ support (BitOracleMachine.run code (PrimeSecondDifferenceMachine.clock q + (PrimeSecondAdjustedMachine.clock p q + (PrimeSecondOneFirstMachine.clock p q + (PrimeSecondOneSecondMachine.clock p q))))
        (BitOracleReturnLink.embed bLabel (some (differenceLabel 0)) v.1)), last.1.l = none := by
    dsimp only [bCode,initial]
    rw [hframe]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    rw [b_source_return,hl]
    intro last hlast
    obtain rfl := eq_of_mem_support_pure _ hlast
    rfl
  have h := BitOracleReturnLink.run bCode code bLabel (differenceLabel 0) b_code
    (PrimeSecondCommitBMachine.clock p q) (PrimeSecondDifferenceMachine.clock q + (PrimeSecondAdjustedMachine.clock p q + (PrimeSecondOneFirstMachine.clock p q + (PrimeSecondOneSecondMachine.clock p q)))) initial hh ht
  dsimp only [bCode,initial] at h
  rw [hframe,pure_bind,b_source_return,hl,pure_bind] at h
  exact ⟨thisCost+lastCost,Nat.add_le_add hc hlc,h⟩

/-- The resident continuation executes all remaining p1 commitment work. -/
theorem execution_source :
    Prod.fst <$> BitOracleMachine.run code (clock p q)
      (start (PrimeSecondCommitMachine.sourceResult slack g pk vote s live out cs).stk) =
      pure (sourceResult slack g pk vote s live out cs) := by
  obtain ⟨charge,_,he⟩ := charged_source slack g pk vote s live out cs
  rw [he,map_pure]

#print axioms charged_source
#print axioms execution_source

#print axioms source_retained
#print axioms source_commitments
#print axioms source_preparation
end ExplainableCrypto.Helios.Computational.PrimeSecondCommitTail
