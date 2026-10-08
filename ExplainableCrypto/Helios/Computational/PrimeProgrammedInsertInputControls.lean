import ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertInputMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertInputControls
open PrimeProgrammedInsertInputMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
private def old : Fin 48 → List Bool := ![[false,false],[true,false],[false,true],[true,true],[false,false],[true,false],[false,true],[true,true],[false,false],[true,false],[false,true],[true,true],[false,false],[true,false],[false,true],[true,true],[false,false],[true,false],[false,true],[true,true],[false,false],[true,false],[false,true],[],[],[true,false],[false,true],[true,true],[false,false],[true,false],[false,true],[true,true],[false,false],[true,false],[false,true],[true,true],[false,false],[true,false],[false,true],[true,true],[false,false],[true,false],[false,true],[true,true],[true,false,true],[true,false],[false,true],[true,true]]
private def expected : Fin 48 → List Bool := ![[false,false],[true,false],[false,true],[true,true],[false,false],[true,false],[false,true],[true,true],[false,false],[true,false],[false,true],[true,true],[false,false],[true,false],[false,true],[true,true],[false,false],[true,false],[false,true],[true,true],[false,false],[true,false],[false,true],[true,false,true],[],[true,false],[false,true],[true,true],[false,false],[true,false],[false,true],[true,true],[false,false],[true,false],[false,true],[true,true],[false,false],[true,false],[false,true],[true,true],[false,false],[true,false],[false,true],[true,true],[],[true,false],[false,true],[true,true]]

theorem literal_run : tick^[13] (start old) = (⟨none,2,expected⟩ : Config) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> decide +kernel
private def skipClear (l : Fin size) := if l = 1 then
  Turing.TM2.Stmt.load (fun _ => (2 : Fin 3)) .halt else program l

theorem omitted_clear_detected :
    ((TM2ReturnLink.tick skipClear)^[13] (start old)).stk 44 = [true,false,true] ∧
    expected 44 = [] := by decide +kernel

theorem failed_entry : tick (⟨some 0,1,old⟩ : Config) = ⟨none,1,old⟩ := rfl
#print axioms literal_run
#print axioms omitted_clear_detected
#print axioms failed_entry
end ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertInputControls
