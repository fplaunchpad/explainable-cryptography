import ExplainableCrypto.Helios.Computational.NatFieldWriterMachine

namespace ExplainableCrypto.Helios.Computational.NatFieldWriterMachine
open Turing.TM2 OracleComp BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
attribute [local irreducible] BitOracleMachine.run

theorem local_cost (l : Fin 21) : localCost (program l) ≤ 32 := by
  fin_cases l <;> decide +kernel
private theorem copy_code (l : Fin 2) : program (copyLabel l) =
    TM2ReturnLink.redirect copyLabel 1 (copyProgram l) := by fin_cases l <;> rfl
private theorem prefix_code (l : Fin 8) : program (prefixLabel l) =
    TM2ReturnLink.redirect prefixLabel 2 (prefixProgram l) := by fin_cases l <;> rfl
private theorem field_code (l : Fin 8) : code (fieldLabel l) =
    BitOracleReturnLink.command fieldLabel none (.compute (fieldProgram l)) := by fin_cases l <;> rfl

private def copied (n : Nat) (suffix : List Bool) : Config :=
  ⟨some 1,0,![n.bits,suffix,[],n.bits,[],[],[]]⟩
private def prefixed (n : Nat) (suffix : List Bool) : Config :=
  ⟨some 2,2,![n.bits,suffix,[],[],uniformNatEncode n,[],[]]⟩
private def copyState (cfg : BitCopyMachine.Config) (frame : Fin 4 → List Bool) :=
  TM2FiniteCoordinates.present (Equiv.refl (Fin 7)) copyLabels BinaryModuloCode.memory
    (TM2StackFrame.embed copyLayout cfg frame)
private def prefixState (cfg : FrameWriteMachine.Config) (frame : Fin 2 → List Bool) :=
  TM2FiniteCoordinates.present (Equiv.refl (Fin 7)) CacheRoutineCode.writerLabels BinaryModuloCode.memory
    (TM2StackFrame.embed prefixLayout cfg frame)
private def fieldState (cfg : FrameWriteMachine.Config) (frame : Fin 2 → List Bool) :=
  TM2FiniteCoordinates.present (Equiv.refl (Fin 7)) CacheRoutineCode.writerLabels BinaryModuloCode.memory
    (TM2StackFrame.embed fieldLayout cfg frame)

private theorem copy_phase (n : Nat) (suffix : List Bool) :
    ∃ u ≤ 2*n.size+2, tick^[u] (⟨some (copyLabel 0),0,![n.bits,suffix,[],[],[],[],[]]⟩ : Config) = copied n suffix := by
  have he := BitCopyMachine.run n.bits [] none
  simp only [List.append_nil,Nat.size_eq_bits_len] at he
  have hc : (TM2ReturnLink.tick copyProgram)^[2*n.size+2]
      (copyState (BitCopyMachine.config (some false) n.bits [] [] none) ![suffix,[],[],[]]) =
      copyState (BitCopyMachine.config none n.bits n.bits [] none) ![suffix,[],[],[]] := by
    unfold copyState copyProgram
    rw [TM2FiniteCoordinates.run,TM2StackFrame.run]
    rw [show TM2ReturnLink.tick BitCopyMachine.program = BitCopyMachine.tick from rfl,he]
  obtain ⟨u,hu,hr⟩ := TM2ReturnLink.run copyProgram program copyLabel 1 copy_code
    (2*n.size+2) _ (by rw [hc]; rfl)
  rw [hc] at hr
  have hi : TM2ReturnLink.embed copyLabel 1
      (copyState (BitCopyMachine.config (some false) n.bits [] [] none) ![suffix,[],[],[]]) =
      (⟨some (copyLabel 0),0,![n.bits,suffix,[],[],[],[],[]]⟩ : Config) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ho : TM2ReturnLink.embed copyLabel 1
      (copyState (BitCopyMachine.config none n.bits n.bits [] none) ![suffix,[],[],[]]) = copied n suffix := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  erw [hi,ho] at hr
  exact ⟨u,hu,hr⟩

private theorem prefix_phase (n : Nat) (suffix : List Bool) :
    ∃ u ≤ 3*n.size+3, tick^[u] (⟨some (prefixLabel 5),0,(copied n suffix).stk⟩ : Config) = prefixed n suffix := by
  have he := FrameWriteMachine.prefix_run n [] none
  simp only [List.append_nil] at he
  have hc : (TM2ReturnLink.tick prefixProgram)^[3*n.size+3]
      (prefixState (FrameWriteMachine.state (some .digits) [] [] [] [] n.bits none) ![n.bits,suffix]) =
      prefixState (FrameWriteMachine.state none [] [] [] (uniformNatEncode n) [] (some true)) ![n.bits,suffix] := by
    unfold prefixState prefixProgram
    rw [TM2FiniteCoordinates.run,TM2StackFrame.run]
    rw [show TM2ReturnLink.tick FrameWriteMachine.program = FrameWriteMachine.tick from rfl,he]
  obtain ⟨u,hu,hr⟩ := TM2ReturnLink.run prefixProgram program prefixLabel 2 prefix_code
    (3*n.size+3) _ (by rw [hc]; rfl)
  rw [hc] at hr
  have hi : TM2ReturnLink.embed prefixLabel 2
      (prefixState (FrameWriteMachine.state (some .digits) [] [] [] [] n.bits none) ![n.bits,suffix]) =
      (⟨some (prefixLabel 5),0,(copied n suffix).stk⟩ : Config) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ho : TM2ReturnLink.embed prefixLabel 2
      (prefixState (FrameWriteMachine.state none [] [] [] (uniformNatEncode n) [] (some true)) ![n.bits,suffix]) = prefixed n suffix := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  erw [hi,ho] at hr
  exact ⟨u,hu,hr⟩

private theorem field_phase (n : Nat) (suffix : List Bool) :
    ∃ u ≤ FrameWriteMachine.cost (2*n.size+1),
      tick^[u] (⟨some (fieldLabel 3),0,(prefixed n suffix).stk⟩ : Config) =
      result n.bits (encoded n suffix) := by
  obtain ⟨u,hu,he⟩ := FrameWriteMachine.run (uniformNatEncode n) suffix
  have hn : (uniformNatEncode n).length = 2*n.size+1 := by
    simp [uniformNatEncode,Nat.size_eq_bits_len]; omega
  rw [hn] at hu
  let cfg := fieldState (FrameWriteMachine.start (uniformNatEncode n) suffix) ![n.bits,[]]
  have hc : (TM2ReturnLink.tick fieldProgram)^[u] cfg =
      fieldState (FrameWriteMachine.state none [] [] [] (encoded n suffix) [] (some true)) ![n.bits,[]] := by
    unfold cfg fieldState fieldProgram
    rw [TM2FiniteCoordinates.run,TM2StackFrame.run]
    rw [show TM2ReturnLink.tick FrameWriteMachine.program = FrameWriteMachine.tick from rfl,he]
    rfl
  have hi : BitOracleReturnLink.embed fieldLabel none cfg =
      (⟨some (fieldLabel 3),0,(prefixed n suffix).stk⟩ : Config) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ho : BitOracleReturnLink.embed fieldLabel none
      (fieldState (FrameWriteMachine.state none [] [] [] (encoded n suffix) [] (some true)) ![n.bits,[]]) =
      result n.bits (encoded n suffix) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  obtain ⟨a,_,ha⟩ := compute_run_cost fieldProgram 32
    (by intro l; fin_cases l <;> decide +kernel) u cfg
  obtain ⟨b,_,hb⟩ := compute_run_cost program 32 local_cost u
    (⟨some (fieldLabel 3),0,(prefixed n suffix).stk⟩ : Config)
  have hr := BitOracleReturnLink.rename_run (fun l => .compute (fieldProgram l)) code fieldLabel field_code u cfg
  rw [ha,hc,map_pure] at hr
  erw [hi,ho,hb] at hr
  have hh := congrArg Prod.fst ((OracleComp.pure_inj _ _).mp hr)
  exact ⟨u,hu,hh⟩

/-- Actual complete encoding from canonical digits; no typed encoding is loaded. -/
theorem run (n : Nat) (suffix : List Bool) :
    ∃ u ≤ clock n, tick^[u] (start n.bits suffix) = result n.bits (encoded n suffix) := by
  obtain ⟨a,ha,he⟩ := copy_phase n suffix
  obtain ⟨b,hb,hf⟩ := prefix_phase n suffix
  obtain ⟨c,hc,hg⟩ := field_phase n suffix
  have h0 : tick (start n.bits suffix) = ⟨some (copyLabel 0),0,![n.bits,suffix,[],[],[],[],[]]⟩ := rfl
  have h1 : tick (copied n suffix) = ⟨some (prefixLabel 5),0,(copied n suffix).stk⟩ := rfl
  have h2 : tick (prefixed n suffix) = ⟨some (fieldLabel 3),0,(prefixed n suffix).stk⟩ := rfl
  refine ⟨c+(1+(b+(1+(a+1)))),by unfold clock; omega,?_⟩
  rw [Function.iterate_add_apply tick c,Function.iterate_add_apply tick 1,
    Function.iterate_add_apply tick b,Function.iterate_add_apply tick 1,
    Function.iterate_succ_apply tick a, h0,he,Function.iterate_one,h1,hf,h2,hg]

/-- Padding is applied only after the complete writer has halted. -/
theorem padded_run (n : Nat) (suffix : List Bool) :
    tick^[clock n] (start n.bits suffix) = result n.bits (encoded n suffix) := by
  obtain ⟨u,hu,he⟩ := run n suffix
  rw [show clock n = (clock n-u)+u by omega,Function.iterate_add_apply,he]
  exact Function.iterate_fixed (show tick (result n.bits (encoded n suffix)) = _ from rfl) _

/-- The full local charge follows from the executed controller and its finite instruction costs. -/
theorem charged (n : Nat) (suffix : List Bool) :
    ∃ charge ≤ cost n,
      BitOracleMachine.run code (clock n) (start n.bits suffix) =
        pure (result n.bits (encoded n suffix),charge) := by
  obtain ⟨charge,hc,he⟩ := compute_run_cost program 32 local_cost (clock n) (start n.bits suffix)
  rw [show (TM2ReturnLink.tick program)^[clock n] (start n.bits suffix) =
    result n.bits (encoded n suffix) from padded_run n suffix] at he
  exact ⟨charge,hc,he⟩

/-- Required by the fixed eight-field caller's modulus-derived clock. -/
theorem clock_mono {n m : Nat} (h : n ≤ m) : clock n ≤ clock m := by
  have hs := Nat.size_le_size h
  have hc := FrameWriteMachine.cost_mono (show 2*n.size+1 ≤ 2*m.size+1 by omega)
  unfold clock
  omega

#print axioms run
#print axioms padded_run
#print axioms charged
#print axioms clock_mono
#print axioms local_cost
end ExplainableCrypto.Helios.Computational.NatFieldWriterMachine
