import ExplainableCrypto.Helios.Computational.BitPairWriterMachine
namespace ExplainableCrypto.Helios.Computational.BitPairWriterMachine
open Turing.TM2 BitOracleMachine OracleComp
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
attribute [local irreducible] BitOracleMachine.run

private theorem copy_code (phase : Fin 2) (l : Fin 2) : program (copyLabel phase l) =
    TM2ReturnLink.redirect (copyLabel phase) (fieldLabel phase 3) (copyProgram phase l) := by
  fin_cases phase <;> fin_cases l <;> rfl
private theorem field_code (phase : Fin 2) (l : Fin 8) : program (fieldLabel phase l) =
    TM2ReturnLink.redirect (fieldLabel phase) (fieldReturn phase) (fieldProgram l) := by
  fin_cases phase <;> fin_cases l <;> rfl

theorem local_cost (l : Fin size) : localCost (program l) ≤ 32 := by
  fin_cases l <;> decide +kernel

private def state (l : Option (Fin size)) (lhs rhs out payload : List Bool) (v : Fin 3 := 0) : Config :=
  ⟨l,v,![lhs,rhs,out,payload,[],[],[]]⟩
private def framed (payload suffix : List Bool) := uniformNatEncode payload.length ++ (payload++suffix)
private def copyState (phase : Fin 2) (cfg : BitCopyMachine.Config) (frame : Fin 4 → List Bool) :=
  TM2FiniteCoordinates.present (Equiv.refl (Fin 7)) NatFieldWriterMachine.copyLabels BinaryModuloCode.memory
    (TM2StackFrame.embed (copyLayout phase) cfg frame)
private def fieldState (cfg : FrameWriteMachine.Config) (frame : Fin 2 → List Bool) :=
  TM2FiniteCoordinates.present (Equiv.refl (Fin 7)) CacheRoutineCode.writerLabels BinaryModuloCode.memory
    (TM2StackFrame.embed fieldLayout cfg frame)

private theorem copy_phase (phase : Fin 2) (lhs rhs suffix : List Bool) :
    ∃ u ≤ 2*(![rhs,lhs] phase).length+2,
      tick^[u] (state (some (copyLabel phase 0)) lhs rhs suffix []) =
      state (some (fieldLabel phase 3)) lhs rhs suffix (![rhs,lhs] phase) := by
  let word := ![rhs,lhs] phase
  let frame : Fin 4 → List Bool := ![![lhs,rhs] phase,suffix,[],[]]
  have he := BitCopyMachine.run word [] none
  simp only [List.append_nil] at he
  have hc : (TM2ReturnLink.tick (copyProgram phase))^[2*word.length+2]
      (copyState phase (BitCopyMachine.config (some false) word [] [] none) frame) =
      copyState phase (BitCopyMachine.config none word word [] none) frame := by
    unfold copyState copyProgram
    rw [TM2FiniteCoordinates.run,TM2StackFrame.run]
    rw [show TM2ReturnLink.tick BitCopyMachine.program = BitCopyMachine.tick from rfl,he]
  obtain ⟨u,hu,hr⟩ := TM2ReturnLink.run (copyProgram phase) program (copyLabel phase) (fieldLabel phase 3)
    (copy_code phase) (2*word.length+2) _ (by rw [hc]; rfl)
  rw [hc] at hr
  have hi : TM2ReturnLink.embed (copyLabel phase) (fieldLabel phase 3)
      (copyState phase (BitCopyMachine.config (some false) word [] [] none) frame) =
      state (some (copyLabel phase 0)) lhs rhs suffix [] := by
    fin_cases phase <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;> rfl
  have ho : TM2ReturnLink.embed (copyLabel phase) (fieldLabel phase 3)
      (copyState phase (BitCopyMachine.config none word word [] none) frame) =
      state (some (fieldLabel phase 3)) lhs rhs suffix (![rhs,lhs] phase) := by
    fin_cases phase <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu,by erw [hi,ho] at hr; exact hr⟩

private theorem field_phase (phase : Fin 2) (lhs rhs payload suffix : List Bool) :
    ∃ u ≤ FrameWriteMachine.cost payload.length,
      tick^[u] (state (some (fieldLabel phase 3)) lhs rhs suffix payload) =
      state (some (fieldReturn phase)) lhs rhs (framed payload suffix) [] 2 := by
  obtain ⟨fuel,hfuel,he⟩ := FrameWriteMachine.run payload suffix
  have hc : (TM2ReturnLink.tick fieldProgram)^[fuel]
      (fieldState (FrameWriteMachine.start payload suffix) ![lhs,rhs]) =
      fieldState (FrameWriteMachine.state none [] [] [] (framed payload suffix) [] (some true)) ![lhs,rhs] := by
    unfold fieldState fieldProgram
    rw [TM2FiniteCoordinates.run,TM2StackFrame.run]
    rw [show TM2ReturnLink.tick FrameWriteMachine.program = FrameWriteMachine.tick from rfl,he]
    rfl
  obtain ⟨u,hu,hr⟩ := TM2ReturnLink.run fieldProgram program (fieldLabel phase) (fieldReturn phase)
    (field_code phase) fuel _ (by rw [hc]; rfl)
  rw [hc] at hr
  have hi : TM2ReturnLink.embed (fieldLabel phase) (fieldReturn phase)
      (fieldState (FrameWriteMachine.start payload suffix) ![lhs,rhs]) =
      state (some (fieldLabel phase 3)) lhs rhs suffix payload := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ho : TM2ReturnLink.embed (fieldLabel phase) (fieldReturn phase)
      (fieldState (FrameWriteMachine.state none [] [] [] (framed payload suffix) [] (some true)) ![lhs,rhs]) =
      state (some (fieldReturn phase)) lhs rhs (framed payload suffix) [] 2 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu.trans hfuel,by erw [hi,ho] at hr; exact hr⟩

/-- The pair codec executes on arbitrary words and preserves both original operands. -/
theorem run (lhs rhs : List Bool) :
    ∃ u ≤ clock lhs.length rhs.length, tick^[u] (start lhs rhs) = result lhs rhs := by
  obtain ⟨a,ha,he⟩ := copy_phase 0 lhs rhs []
  obtain ⟨b,hb,hf⟩ := field_phase 0 lhs rhs rhs []
  obtain ⟨c,hc,hg⟩ := copy_phase 1 lhs rhs (framed rhs [])
  obtain ⟨d,hd,hh⟩ := field_phase 1 lhs rhs lhs (framed rhs [])
  have h0 : tick (start lhs rhs) = state (some (copyLabel 0 0)) lhs rhs [] [] := rfl
  have h1 : tick (state (some 1) lhs rhs (framed rhs []) [] 2) =
      state (some (copyLabel 1 0)) lhs rhs (framed rhs []) [] := rfl
  have h2 : tick (state (some 2) lhs rhs (framed lhs (framed rhs [])) [] 2) = result lhs rhs := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> simp [framed,bitFieldsEncode,bitFramesEncode,List.append_assoc,
      show uniformNatEncode 2=[true,true,false,false,true] from rfl]
  refine ⟨1+(d+(c+(1+(b+(a+1))))),?_,?_⟩
  · change a ≤ 2*rhs.length+2 at ha
    change c ≤ 2*lhs.length+2 at hc
    unfold clock
    omega
  · erw [Function.iterate_add_apply tick 1,Function.iterate_add_apply tick d,
      Function.iterate_add_apply tick c,Function.iterate_add_apply tick 1,
      Function.iterate_add_apply tick b,Function.iterate_succ_apply tick a,h0,he,hf,
      Function.iterate_one,h1,hg,hh,h2]

/-- Fixed-clock execution follows by padding the actual halted result. -/
theorem padded_run (lhs rhs : List Bool) :
    tick^[clock lhs.length rhs.length] (start lhs rhs) = result lhs rhs := by
  obtain ⟨u,hu,he⟩ := run lhs rhs
  rw [show clock lhs.length rhs.length=(clock lhs.length rhs.length-u)+u by omega,
    Function.iterate_add_apply,he]
  exact Function.iterate_fixed (show tick (result lhs rhs) = _ from rfl) _

/-- Required for the fixed nested proof/cache record caller's operand bounds. -/
theorem clock_mono {L R A B : Nat} (hL : L ≤ A) (hR : R ≤ B) : clock L R ≤ clock A B := by
  have hl := FrameWriteMachine.cost_mono hL
  have hr := FrameWriteMachine.cost_mono hR
  unfold clock
  omega

/-- Enclosing length bounds only pad a run that already derives its complete endpoint. -/
theorem padded_bounded (lhs rhs : List Bool) (L R : Nat) (hL : lhs.length ≤ L) (hR : rhs.length ≤ R) :
    tick^[clock L R] (start lhs rhs) = result lhs rhs := by
  obtain ⟨u,hu,he⟩ := run lhs rhs
  have hu' := hu.trans (clock_mono hL hR)
  rw [show clock L R=(clock L R-u)+u by omega,Function.iterate_add_apply,he]
  exact Function.iterate_fixed (show tick (result lhs rhs) = _ from rfl) _

/-- Actual finite-controller charge on the same bounded pair run. -/
theorem charged_bounded (lhs rhs : List Bool) (L R : Nat) (hL : lhs.length ≤ L) (hR : rhs.length ≤ R) :
    ∃ charge ≤ cost L R, BitOracleMachine.run code (clock L R) (start lhs rhs) = pure (result lhs rhs,charge) := by
  obtain ⟨charge,hc,he⟩ := compute_run_cost program 32 local_cost (clock L R) (start lhs rhs)
  rw [show (TM2ReturnLink.tick program)^[clock L R] (start lhs rhs) = result lhs rhs from
    padded_bounded lhs rhs L R hL hR] at he
  exact ⟨charge,hc,he⟩

theorem charged (lhs rhs : List Bool) :
    ∃ charge ≤ cost lhs.length rhs.length,
      BitOracleMachine.run code (clock lhs.length rhs.length) (start lhs rhs) = pure (result lhs rhs,charge) :=
  charged_bounded lhs rhs _ _ le_rfl le_rfl

#print axioms run
#print axioms padded_run
#print axioms clock_mono
#print axioms padded_bounded
#print axioms charged_bounded
#print axioms charged
end ExplainableCrypto.Helios.Computational.BitPairWriterMachine
