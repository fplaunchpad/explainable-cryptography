import ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextMachine

namespace ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextMachine
open Turing.TM2
set_option maxRecDepth 8192

private theorem copy_code (l : Fin 2) : program (copyLabel l) =
    TM2ReturnLink.redirect copyLabel (parseLabel 0) (copyProgram l) := by
  fin_cases l <;> rfl
private theorem parse_code (l : Fin 3) : program (parseLabel l) =
    TM2ReturnLink.redirect parseLabel 1 (parseProgram l) := by
  fin_cases l <;> rfl

private def state (l : Option (Fin 7)) (input nonce record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) (v : Fin 3 := 0) : Config :=
  ⟨l,v,![[],[],[],[],[],[],modulus,input,[],[],[],[],[],nonce,context,pk,g,[],[vote],record,first,second,samplerMod]⟩

private theorem copy_run (record first second samplerMod context modulus g pk : List Bool) (vote : Bool) :
    ∃ used ≤ 2*first.length+2,
      tick^[used] (state (some (copyLabel 0)) [] [] record first second samplerMod context modulus g pk vote) =
      state (some (parseLabel 0)) first [] record first second samplerMod context modulus g pk vote := by
  let initial := TM2FiniteCoordinates.present copyPorts copyLabels BinaryModuloCode.memory
    (BitCopyMachine.config (some false) first [] [])
  let final := TM2FiniteCoordinates.present copyPorts copyLabels BinaryModuloCode.memory
    (BitCopyMachine.config none first first [])
  let frame : Fin 20 → List Bool :=
    ![[],[],[],[],[],modulus,[],[],[],[],[],[],context,pk,g,[],[vote],record,second,samplerMod]
  have hi : (TM2ReturnLink.tick
      (TM2FiniteCoordinates.program copyPorts copyLabels BinaryModuloCode.memory BitCopyMachine.program))^[2*first.length+2]
      initial = final := by
    dsimp only [initial]
    rw [TM2FiniteCoordinates.run]
    rw [show (TM2ReturnLink.tick BitCopyMachine.program)^[2*first.length+2]
      (BitCopyMachine.config (some false) first [] []) =
      BitCopyMachine.config none first (first++[]) [] from BitCopyMachine.run first [] none]
    simp only [List.append_nil]
    rfl
  have hf := TM2StackFrame.run copyLayout
    (TM2FiniteCoordinates.program copyPorts copyLabels BinaryModuloCode.memory BitCopyMachine.program)
    (2*first.length+2) initial frame
  rw [hi] at hf
  change (TM2ReturnLink.tick copyProgram)^[2*first.length+2]
    (TM2StackFrame.embed copyLayout initial frame) = TM2StackFrame.embed copyLayout final frame at hf
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run copyProgram program copyLabel (parseLabel 0)
    copy_code (2*first.length+2) _ (by rw [hf]; rfl)
  rw [hf] at he
  have hs : TM2ReturnLink.embed copyLabel (parseLabel 0) (TM2StackFrame.embed copyLayout initial frame) =
      state (some (copyLabel 0)) [] [] record first second samplerMod context modulus g pk vote := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ht : TM2ReturnLink.embed copyLabel (parseLabel 0) (TM2StackFrame.embed copyLayout final frame) =
      state (some (parseLabel 0)) first [] record first second samplerMod context modulus g pk vote := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu,by rwa [hs,ht] at he⟩

private theorem parse_run (n : Nat) (record second samplerMod context modulus g pk : List Bool) (vote : Bool) :
    ∃ used ≤ 3*n.size+3,
      tick^[used] (state (some (parseLabel 0)) (uniformNatEncode n) [] record (uniformNatEncode n)
        second samplerMod context modulus g pk vote) =
      state (some 1) [] n.bits record (uniformNatEncode n) second samplerMod context modulus g pk vote 2 := by
  let initial := TM2FiniteCoordinates.present parsePorts parseLabels BinaryModuloCode.memory
    (NatPrefixMachine.start (uniformNatEncode n))
  let final := TM2FiniteCoordinates.present parsePorts parseLabels BinaryModuloCode.memory
    (NatPrefixMachine.config none [] [] [] n.bits (some true))
  let frame : Fin 19 → List Bool :=
    ![[],[],[],[],modulus,[],[],[],[],[],context,pk,g,[],[vote],record,uniformNatEncode n,second,samplerMod]
  have hi : (TM2ReturnLink.tick
      (TM2FiniteCoordinates.program parsePorts parseLabels BinaryModuloCode.memory NatPrefixMachine.program))^[3*n.size+3]
      initial = final := by
    dsimp only [initial]
    rw [TM2FiniteCoordinates.run]
    have h := NatPrefixMachine.encoded_run n []
    simp only [List.append_nil] at h
    change (TM2ReturnLink.tick NatPrefixMachine.program)^[3*n.size+3] _ = _ at h
    rw [h]
  have hf := TM2StackFrame.run parseLayout
    (TM2FiniteCoordinates.program parsePorts parseLabels BinaryModuloCode.memory NatPrefixMachine.program)
    (3*n.size+3) initial frame
  rw [hi] at hf
  change (TM2ReturnLink.tick parseProgram)^[3*n.size+3]
    (TM2StackFrame.embed parseLayout initial frame) = TM2StackFrame.embed parseLayout final frame at hf
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run parseProgram program parseLabel 1
    parse_code (3*n.size+3) _ (by rw [hf]; rfl)
  rw [hf] at he
  have hs : TM2ReturnLink.embed parseLabel 1 (TM2StackFrame.embed parseLayout initial frame) =
      state (some (parseLabel 0)) (uniformNatEncode n) [] record (uniformNatEncode n)
        second samplerMod context modulus g pk vote := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ht : TM2ReturnLink.embed parseLabel 1 (TM2StackFrame.embed parseLayout final frame) =
      state (some 1) [] n.bits record (uniformNatEncode n) second samplerMod context modulus g pk vote 2 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu,by rwa [hs,ht] at he⟩

/-- Execute the saved first prefix into the exact encryption nonce port. Both
nonce prefixes, both modulus words, record, context and input coordinates remain. -/
theorem run (n : Nat) (record second samplerMod context modulus g pk : List Bool) (vote : Bool) :
    ∃ used ≤ clock n,
      tick^[used] (start record (uniformNatEncode n) second samplerMod context modulus g pk vote) =
      result n.bits record (uniformNatEncode n) second samplerMod context modulus g pk vote := by
  obtain ⟨u,hu,hcopy⟩ := copy_run record (uniformNatEncode n) second samplerMod context modulus g pk vote
  obtain ⟨v,hv,hparse⟩ := parse_run n record second samplerMod context modulus g pk vote
  have hstart : tick (start record (uniformNatEncode n) second samplerMod context modulus g pk vote) =
      state (some (copyLabel 0)) [] [] record (uniformNatEncode n) second samplerMod context modulus g pk vote := rfl
  have hfinish : tick (state (some 1) [] n.bits record (uniformNatEncode n) second samplerMod context modulus g pk vote 2) =
      result n.bits record (uniformNatEncode n) second samplerMod context modulus g pk vote := rfl
  refine ⟨1+(v+u)+1,?_,?_⟩
  · rw [uniformNatEncode_length] at hu
    unfold clock
    omega
  · rw [Function.iterate_succ_apply,hstart,Function.iterate_add_apply tick 1 (v+u),Function.iterate_one,Function.iterate_add_apply,hcopy,hparse,hfinish]

/-- Fixed caller width absorbs unused ticks only after final halt. -/
theorem padded_run_bounded (n bound : Nat) (hn : n ≤ bound)
    (record second samplerMod context modulus g pk : List Bool) (vote : Bool) :
    tick^[clock bound] (start record (uniformNatEncode n) second samplerMod context modulus g pk vote) =
      result n.bits record (uniformNatEncode n) second samplerMod context modulus g pk vote := by
  obtain ⟨u,hu,he⟩ := run n record second samplerMod context modulus g pk vote
  have hw := Nat.size_le_size hn
  have hb : u ≤ clock bound := by unfold clock at *; omega
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hb
  rw [hd,Nat.add_comm u d,Function.iterate_add_apply,he]
  exact Function.iterate_fixed (by rfl) d

/-- Exact natural-dependent clock for the complete saved-word handoff. -/
theorem padded_run (n : Nat) (record second samplerMod context modulus g pk : List Bool) (vote : Bool) :
    tick^[clock n] (start record (uniformNatEncode n) second samplerMod context modulus g pk vote) =
      result n.bits record (uniformNatEncode n) second samplerMod context modulus g pk vote :=
  padded_run_bounded n n le_rfl record second samplerMod context modulus g pk vote

/-- Finite audit of the actual copy, parsing and guard statements. -/
theorem local_cost (l : Fin 7) : BitOracleMachine.localCost (program l) ≤ 6 := by
  fin_cases l <;> decide +kernel

/-- The q-wide caller obtains actual charged execution from the derived size
bound, without supplying a runtime certificate or correspondence premise. -/
theorem charged_bounded (n bound : Nat) (hn : n ≤ bound)
    (record second samplerMod context modulus g pk : List Bool) (vote : Bool) :
    ∃ charge ≤ 6*clock bound,
      BitOracleMachine.run code (clock bound)
        (start record (uniformNatEncode n) second samplerMod context modulus g pk vote) =
      pure (result n.bits record (uniformNatEncode n) second samplerMod context modulus g pk vote,charge) := by
  obtain ⟨c,hc,he⟩ := BitOracleMachine.compute_run_cost program 6 local_cost (clock bound)
    (start record (uniformNatEncode n) second samplerMod context modulus g pk vote)
  refine ⟨c,hc,?_⟩
  change BitOracleMachine.run code (clock bound)
    (start record (uniformNatEncode n) second samplerMod context modulus g pk vote) =
    pure (tick^[clock bound] (start record (uniformNatEncode n) second samplerMod context modulus g pk vote),c) at he
  rw [he,padded_run_bounded n bound hn record second samplerMod context modulus g pk vote]

theorem charged (n : Nat) (record second samplerMod context modulus g pk : List Bool) (vote : Bool) :
    ∃ charge ≤ 6*clock n,
      BitOracleMachine.run code (clock n)
        (start record (uniformNatEncode n) second samplerMod context modulus g pk vote) =
      pure (result n.bits record (uniformNatEncode n) second samplerMod context modulus g pk vote,charge) :=
  charged_bounded n n le_rfl record second samplerMod context modulus g pk vote

/-- The actual typed scalar derives the fixed q−1 caller clock. -/
theorem scalar_clock_le {q : Nat} [NeZero q] (r : ZMod q) : clock r.val ≤ clock (q-1) := by
  have hv : r.val ≤ q-1 := by have := r.val_lt; omega
  have hw := Nat.size_le_size hv
  unfold clock
  omega

#print axioms run
#print axioms padded_run_bounded
#print axioms padded_run
#print axioms local_cost
#print axioms charged_bounded
#print axioms charged
#print axioms scalar_clock_le
end ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextMachine
