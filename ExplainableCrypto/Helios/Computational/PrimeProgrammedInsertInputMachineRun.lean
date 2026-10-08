import ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertInputMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertInputMachine
open Turing.TM2 OracleComp
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

private theorem copy_code (l : Fin 2) : program (copyLabel l) =
    TM2ReturnLink.redirect copyLabel 1 (copyProgram l) := by
  fin_cases l <;> rfl

private theorem copy_run (old : Fin 48 → List Bool) (h23 : old 23 = []) (h24 : old 24 = []) :
    ∃ u ≤ 2*(old 44).length+2,
      tick^[u] ⟨some (copyLabel 0),0,old⟩ =
        ⟨some 1,0,Function.update old 23 (old 44)⟩ := by
  let ports := PrimeNonceCiphertextMachine.copyPorts
  let labels := PrimeNonceCiphertextMachine.copyLabels
  let initial := TM2FiniteCoordinates.present ports labels BinaryModuloCode.memory
    (BitCopyMachine.config (some false) (old 44) [] [])
  let final := TM2FiniteCoordinates.present ports labels BinaryModuloCode.memory
    (BitCopyMachine.config none (old 44) (old 44) [])
  let frame : Fin 45 → List Bool := fun j => old (copyLayout (.inr j))
  have hi : (TM2ReturnLink.tick
      (TM2FiniteCoordinates.program ports labels BinaryModuloCode.memory BitCopyMachine.program))^[2*(old 44).length+2]
      initial = final := by
    dsimp only [initial]
    rw [TM2FiniteCoordinates.run]
    rw [show (TM2ReturnLink.tick BitCopyMachine.program)^[2*(old 44).length+2]
      (BitCopyMachine.config (some false) (old 44) [] []) =
      BitCopyMachine.config none (old 44) ((old 44)++[]) [] from BitCopyMachine.run _ [] none]
    simp only [List.append_nil]
    rfl
  have hf := TM2StackFrame.run copyLayout
    (TM2FiniteCoordinates.program ports labels BinaryModuloCode.memory BitCopyMachine.program)
    (2*(old 44).length+2) initial frame
  rw [hi] at hf
  change (TM2ReturnLink.tick copyProgram)^[2*(old 44).length+2]
    (TM2StackFrame.embed copyLayout initial frame) = TM2StackFrame.embed copyLayout final frame at hf
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run copyProgram program copyLabel 1
    copy_code (2*(old 44).length+2) _ (by rw [hf]; rfl)
  rw [hf] at he
  have hs : TM2ReturnLink.embed copyLabel 1 (TM2StackFrame.embed copyLayout initial frame) =
      (⟨some (copyLabel 0),0,old⟩ : Config) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    funext k
    fin_cases k <;> first | rfl | exact h23.symm | exact h24.symm
  have ht : TM2ReturnLink.embed copyLabel 1 (TM2StackFrame.embed copyLayout final frame) =
      (⟨some 1,0,Function.update old 23 (old 44)⟩ : Config) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    funext k
    fin_cases k <;> first | rfl | exact h24.symm
  refine ⟨u,hu,?_⟩
  change (TM2ReturnLink.tick program)^[u] _ = _
  rwa [hs,ht] at he

private theorem clear_run (words : Fin 48 → List Bool) (word : List Bool) (v : Fin 3) :
    tick^[word.length+1] ⟨some 1,v,Function.update words 44 word⟩ =
      ⟨none,2,Function.update words 44 []⟩ := by
  induction word generalizing v with
  | nil =>
    simp [tick,TM2ReturnLink.tick,program,stepAux,Function.update,BinaryModuloCode.memory]
  | cons bit word ih =>
    have hs : tick (⟨some 1,v,Function.update words 44 (bit::word)⟩ : Config) =
        ⟨some 1,BinaryModuloCode.memory (some bit),Function.update words 44 word⟩ := by
      cases bit <;> simp [tick,TM2ReturnLink.tick,program,stepAux,Function.update,BinaryModuloCode.memory]
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,hs,ih]

/-- Actual copy then destructive source cleanup preserves all other48-port words. -/
theorem run (old : Fin 48 → List Bool) (h23 : old 23 = []) (h24 : old 24 = []) :
    ∃ used ≤ clock (old 44), tick^[used] (start old) = result old := by
  obtain ⟨u,hu,he⟩ := copy_run old h23 h24
  have hs : tick (start old) = (⟨some (copyLabel 0),0,old⟩ : Config) := rfl
  have hc := clear_run (Function.update old 23 (old 44)) (old 44) 0
  have hi : (Function.update (Function.update old 23 (old 44)) 44 (old 44)) =
      Function.update old 23 (old 44) := by
    funext k
    by_cases h : k = 44
    · subst k; simp
    · simp [Function.update,h]
  rw [hi] at hc
  have first : tick^[u+1] (start old) = (⟨some 1,0,Function.update old 23 (old 44)⟩ : Config) := by
    rw [Function.iterate_succ_apply,hs,he]
  refine ⟨(old 44).length+1+(u+1),by unfold clock; omega,?_⟩
  rw [Function.iterate_add_apply,first,hc]
  rfl

/-- Padding occurs only after the derived complete halting result. -/
theorem padded_run (old : Fin 48 → List Bool) (h23 : old 23 = []) (h24 : old 24 = []) :
    tick^[clock (old 44)] (start old) = result old := by
  obtain ⟨u,hu,he⟩ := run old h23 h24
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hu
  rw [hd,Nat.add_comm u d,Function.iterate_add_apply,he]
  exact Function.iterate_fixed (by rfl) d

theorem local_cost (l : Fin size) : BitOracleMachine.localCost (program l) ≤ 32 := by
  fin_cases l <;> decide +kernel

/-- Charge is derived from actual instructions, not a supplied bound. -/
theorem charged (old : Fin 48 → List Bool) (h23 : old 23 = []) (h24 : old 24 = []) :
    ∃ charge ≤ cost (old 44), BitOracleMachine.run code (clock (old 44)) (start old) =
      pure (result old,charge) := by
  obtain ⟨charge,hc,he⟩ := BitOracleMachine.compute_run_cost program 32 local_cost
    (clock (old 44)) (start old)
  rw [show (TM2ReturnLink.tick program)^[clock (old 44)] (start old) = result old from
    padded_run old h23 h24] at he
  exact ⟨charge,hc,he⟩

/-- Uniform padding for an enclosing caller with a derived cache-word bound. -/
theorem charged_bounded (old : Fin 48 → List Bool) (N : Nat)
    (h23 : old 23 = []) (h24 : old 24 = []) (hcache : (old 44).length ≤ N) :
    ∃ charge ≤ 32*(3*N+4),
      BitOracleMachine.run code (3*N+4) (start old) = pure (result old,charge) := by
  have hp : tick^[3*N+4] (start old) = result old := by
    obtain ⟨u,hu,he⟩ := run old h23 h24
    have hb : u ≤ 3*N+4 := by unfold clock at hu; omega
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hb
    rw [hd,Nat.add_comm u d,Function.iterate_add_apply,he]
    exact Function.iterate_fixed (by rfl) d
  obtain ⟨charge,hc,he⟩ := BitOracleMachine.compute_run_cost program 32 local_cost (3*N+4) (start old)
  rw [show (TM2ReturnLink.tick program)^[3*N+4] (start old) = result old from hp] at he
  exact ⟨charge,hc,he⟩

#print axioms charged_bounded
#print axioms run
#print axioms padded_run
#print axioms local_cost
#print axioms charged
end ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertInputMachine
