import ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachineRun

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachineControls
open PrimeProgrammedStateInputMachine Turing.TM2 BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

private def old0 : Fin 44 → List Bool :=
  ![[true],
  [true,true,false,false,true],
  [true,true],
  [true],
  [],
  [],
  [true,true,true],
  [true,true,false,false,true],
  [],
  [],
  [false],
  [true,false,true],
  [true,false,true],
  [true],
  [true,true,true,false,true,false,true,false,false,false,false,true,true,true,true,true,true,false,false,true,false,true,false,true,true,true,false,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,false,true,true,true,true,false,false,true,false,true,true,true,false,false,true,true,false,true,false,false,false],
  [false,false,true],
  [false,true],
  [false,true],
  [true],
  [false,true,true,false,true,true],
  [true,false,true],
  [true,true,false,false,true],
  [false,true],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [false,false,true],
  [false,false,true],
  [true],
  [],
  [true],
  [true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true]]
private def expected0 : Fin 48 → List Bool :=
  ![[true],
  [true,true,false,false,true],
  [true,true],
  [true],
  [],
  [],
  [true,true,true],
  [true,true,false,false,true],
  [],
  [],
  [false],
  [true,false,true],
  [true,false,true],
  [true],
  [true,true,true,false,true,false,true,false,false,false,false,true,true,true,true,true,true,false,false,true,false,true,false,true,true,true,false,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,false,true,true,true,true,false,false,true,false,true,true,true,false,false,true,true,false,true,false,false,false],
  [false,false,true],
  [false,true],
  [false,true],
  [true],
  [false,true,true,false,true,true],
  [true,false,true],
  [true,true,false,false,true],
  [false,true],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [false,false,true],
  [false,false,true],
  [true],
  [],
  [true],
  [true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true],
  [],
  [],
  [false],
  []]

theorem empty_payloads_full_state :
    tick^[clock (old0 14).length] (start old0) = (⟨none,2,expected0⟩ : Config) := by
  rw [padded_run [] [] [] [] [] [] [] false old0 rfl (by intro j; fin_cases j <;> rfl)]
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext j; fin_cases j <;> rfl
#print axioms empty_payloads_full_state

private def old1 : Fin 44 → List Bool :=
  ![[true],
  [true,true,false,false,true],
  [true,true],
  [true],
  [],
  [],
  [true,true,true],
  [true,true,false,false,true],
  [],
  [],
  [false],
  [true,false,true],
  [true,false,true],
  [true],
  [true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,true,true,true,true,true,false,true,true,false,true,false,false,true,true,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,false,true,true,false,true,true,true,false,false,true,true,false,true,true,true,true,true,false,false,true,true,true,false,true,true,false,true,true,true,true,false,false,false,true,false,true,true,false],
  [false,false,true],
  [false,true],
  [false,true],
  [true],
  [false,true,true,false,true,true],
  [true,false,true],
  [true,true,false,false,true],
  [false,true],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [false,false,true],
  [false,false,true],
  [true],
  [],
  [true],
  [true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true]]
private def expected1 : Fin 48 → List Bool :=
  ![[true],
  [true,true,false,false,true],
  [true,true],
  [true],
  [],
  [],
  [true,true,true],
  [true,true,false,false,true],
  [],
  [],
  [false],
  [true,false,true],
  [true,false,true],
  [true],
  [true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,true,true,true,true,true,false,true,true,false,true,false,false,true,true,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,false,true,true,false,true,true,true,false,false,true,true,false,true,true,true,true,true,false,false,true,true,true,false,true,true,false,true,true,true,true,false,false,false,true,false,true,true,false],
  [false,false,true],
  [false,true],
  [false,true],
  [true],
  [false,true,true,false,true,true],
  [true,false,true],
  [true,true,false,false,true],
  [false,true],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [false,false,true],
  [false,false,true],
  [true],
  [],
  [true],
  [true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true],
  [true,false,true],
  [false,true,true,false],
  [true],
  [true,false,true,true,false,true]]

theorem distinct_payloads_full_state :
    tick^[clock (old1 14).length] (start old1) = (⟨none,2,expected1⟩ : Config) := by
  rw [padded_run [true,true,true,false,true,true,true] [true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true] [false,true,true,false,true,true] [true] [true,false,true] [false,true,true,false] [true,false,true,true,false,true] true old1 rfl (by intro j; fin_cases j <;> rfl)]
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext j; fin_cases j <;> rfl
#print axioms distinct_payloads_full_state

private def longFlag : Config := ⟨some 16,0,Function.update expected1 46 [true,false]⟩
private def bypassFlag (l : Fin size) :=
  if l == 16 then Stmt.load (fun _ : Fin 3 => 2) Stmt.halt else program l

/-- The original final instruction consumes the first flag bit and rejects the trailing bit. -/
theorem long_flag_rejected : tick longFlag =
    (⟨none,1,Function.update expected1 46 [false]⟩ : Config) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext j; fin_cases j <;> rfl

/-- This is the same actual flag-guard bypass used in the full native gate. -/
theorem flag_guard_bypass_accepts : TM2ReturnLink.tick bypassFlag longFlag =
    (⟨none,2,Function.update expected1 46 [true,false]⟩ : Config) := rfl

theorem clock_small_controls : clock 0 = 118 ∧ clock 1 = 212 ∧ clock 2 = 350 ∧ clock 3 = 433 := by decide

theorem constant_only_refuted : ¬ clock 1 ≤ 118 := by decide

#print axioms long_flag_rejected
#print axioms flag_guard_bypass_accepts
#print axioms clock_small_controls
#print axioms constant_only_refuted
end ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachineControls
