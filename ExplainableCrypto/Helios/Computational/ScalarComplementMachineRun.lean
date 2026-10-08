import ExplainableCrypto.Helios.Computational.ScalarComplementMachine

namespace ExplainableCrypto.Helios.Computational.ScalarComplementMachine
open Turing.TM2
set_option maxRecDepth 8192

private theorem copy_code (which : Bool) (l : Fin 2) : program (copyLabel which l) =
    TM2ReturnLink.redirect (copyLabel which) (if which then subLabel 0 else parseLabel 0)
      (copyProgram which l) := by
  cases which <;> fin_cases l <;> rfl
private theorem parse_code (l : Fin 3) : program (parseLabel l) =
    TM2ReturnLink.redirect parseLabel 1 (parseProgram l) := by
  fin_cases l <;> rfl
private theorem sub_code (l : Fin 11) : program (subLabel l) =
    TM2ReturnLink.redirect subLabel 2 (subProgram l) := by
  fin_cases l <;> rfl

private def copyPresent (phase : Option Bool) (src dst scratch : List Bool) :=
  TM2FiniteCoordinates.present PrimeNonceCiphertextMachine.copyPorts
    PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory
    (BitCopyMachine.config phase src dst scratch)

private theorem copy_run (which : Bool) (word : List Bool) (frame : Fin 5 → List Bool) :
    ∃ used ≤ 2*word.length+2,
      tick^[used]
        (TM2ReturnLink.embed (copyLabel which) (if which then subLabel 0 else parseLabel 0)
          (TM2StackFrame.embed (copyLayout which) (copyPresent (some false) word [] []) frame)) =
        TM2ReturnLink.embed (copyLabel which) (if which then subLabel 0 else parseLabel 0)
          (TM2StackFrame.embed (copyLayout which) (copyPresent none word word []) frame) := by
  have hi : (TM2ReturnLink.tick
      (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.copyPorts
        PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory BitCopyMachine.program))^[2*word.length+2]
      (copyPresent (some false) word [] []) = copyPresent none word word [] := by
    unfold copyPresent
    rw [TM2FiniteCoordinates.run]
    have h := BitCopyMachine.run word [] none
    simp only [List.append_nil] at h
    change (TM2ReturnLink.tick BitCopyMachine.program)^[2*word.length+2] _ = _ at h
    rw [h]
  have hf := TM2StackFrame.run (copyLayout which)
    (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.copyPorts
      PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory BitCopyMachine.program)
    (2*word.length+2) (copyPresent (some false) word [] []) frame
  rw [hi] at hf
  change (TM2ReturnLink.tick (copyProgram which))^[2*word.length+2]
    (TM2StackFrame.embed (copyLayout which) (copyPresent (some false) word [] []) frame) =
    TM2StackFrame.embed (copyLayout which) (copyPresent none word word []) frame at hf
  obtain ⟨used,hu,he⟩ := TM2ReturnLink.run (copyProgram which) program (copyLabel which)
    (if which then subLabel 0 else parseLabel 0) (copy_code which) (2*word.length+2) _ (by rw [hf]; rfl)
  rw [hf] at he
  exact ⟨used,hu,he⟩

private def state (phase : Option (Fin 21)) (q record temp e complement : List Bool) (v : Fin 3 := 0) : Config :=
  ⟨phase,v,![q,record,temp,[],[],e,[],complement]⟩

private theorem parse_run (e : Nat) (q record : List Bool) :
    ∃ used ≤ 3*e.size+3,
      tick^[used] (state (some (parseLabel 0)) q record (uniformNatEncode e) [] []) =
      state (some 1) q record [] e.bits [] 2 := by
  let initial := TM2FiniteCoordinates.present PrimeNonceCiphertextMachine.parsePorts
    PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory
    (NatPrefixMachine.start (uniformNatEncode e))
  let final := TM2FiniteCoordinates.present PrimeNonceCiphertextMachine.parsePorts
    PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory
    (NatPrefixMachine.config none [] [] [] e.bits (some true))
  let frame : Fin 4 → List Bool := ![q,record,[],[]]
  have hi : (TM2ReturnLink.tick
      (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.parsePorts
        PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory NatPrefixMachine.program))^[3*e.size+3]
      initial = final := by
    dsimp only [initial]
    rw [TM2FiniteCoordinates.run]
    have h := NatPrefixMachine.encoded_run e []
    simp only [List.append_nil] at h
    change (TM2ReturnLink.tick NatPrefixMachine.program)^[3*e.size+3] _ = _ at h
    rw [h]
  have hf := TM2StackFrame.run parseLayout
    (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.parsePorts
      PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory NatPrefixMachine.program)
    (3*e.size+3) initial frame
  rw [hi] at hf
  change (TM2ReturnLink.tick parseProgram)^[3*e.size+3]
    (TM2StackFrame.embed parseLayout initial frame) = TM2StackFrame.embed parseLayout final frame at hf
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run parseProgram program parseLabel 1
    parse_code (3*e.size+3) _ (by rw [hf]; rfl)
  rw [hf] at he
  have hs : TM2ReturnLink.embed parseLabel 1 (TM2StackFrame.embed parseLayout initial frame) =
      state (some (parseLabel 0)) q record (uniformNatEncode e) [] [] := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ht : TM2ReturnLink.embed parseLabel 1 (TM2StackFrame.embed parseLayout final frame) =
      state (some 1) q record [] e.bits [] 2 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu,by rwa [hs,ht] at he⟩

private theorem sub_run (q e : Nat) (heq : e < q) (record : List Bool) :
    ∃ used ≤ 3*(q.size+e.size)+5,
      tick^[used] (state (some (subLabel 0)) q.bits record q.bits e.bits []) =
      state (some 2) q.bits record [] e.bits (q-e).bits 2 := by
  let initial := TM2FiniteCoordinates.present BinaryModAddMachine.subPorts
    BinaryModAddMachine.subLabels BinaryModuloCode.memory
    (BinarySubtractMachine.state (some (.scan false)) q.bits e.bits [] [] [] [])
  let final := TM2FiniteCoordinates.present BinaryModAddMachine.subPorts
    BinaryModAddMachine.subLabels BinaryModuloCode.memory
    (BinarySubtractMachine.state none [] e.bits [] [] [] (q-e).bits (some true))
  let frame : Fin 2 → List Bool := ![q.bits,record]
  obtain ⟨u,hu,he⟩ := BinarySubtractMachine.run q.bits e.bits
  simp only [Nat.size_eq_bits_len] at hu
  simp only [bitsValue_bits,if_pos heq.le,decide_eq_true heq.le] at he
  have hi : (TM2ReturnLink.tick
      (TM2FiniteCoordinates.program BinaryModAddMachine.subPorts BinaryModAddMachine.subLabels
        BinaryModuloCode.memory BinarySubtractMachine.program))^[u] initial = final := by
    dsimp only [initial]
    rw [TM2FiniteCoordinates.run]
    change (TM2ReturnLink.tick BinarySubtractMachine.program)^[u] _ = _ at he
    rw [he]
  have hf := TM2StackFrame.run subLayout
    (TM2FiniteCoordinates.program BinaryModAddMachine.subPorts BinaryModAddMachine.subLabels
      BinaryModuloCode.memory BinarySubtractMachine.program) u initial frame
  rw [hi] at hf
  change (TM2ReturnLink.tick subProgram)^[u] (TM2StackFrame.embed subLayout initial frame) =
    TM2StackFrame.embed subLayout final frame at hf
  obtain ⟨v,hv,hv'⟩ := TM2ReturnLink.run subProgram program subLabel 2 sub_code u _ (by rw [hf]; rfl)
  rw [hf] at hv'
  have hs : TM2ReturnLink.embed subLabel 2 (TM2StackFrame.embed subLayout initial frame) =
      state (some (subLabel 0)) q.bits record q.bits e.bits [] := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ht : TM2ReturnLink.embed subLabel 2 (TM2StackFrame.embed subLayout final frame) =
      state (some 2) q.bits record [] e.bits (q-e).bits 2 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  exact ⟨v,by simpa only [Nat.size_eq_bits_len] using hv.trans hu,by rwa [hs,ht] at hv'⟩

/-- Both input copies, canonical scalar decoding and q-e subtraction execute
in the fixed controller. The zero scalar returns q, the intended group exponent. -/
theorem run (q e : Nat) (he : e < q) :
    ∃ used ≤ clock q,
      tick^[used] (start q.bits (uniformNatEncode e)) =
      result q.bits (uniformNatEncode e) e.bits (q-e).bits := by
  obtain ⟨u,hu,hcopy⟩ := copy_run false (uniformNatEncode e) ![q.bits,[],[],[],[]]
  have hcs : TM2ReturnLink.embed (copyLabel false) (if false then subLabel 0 else parseLabel 0)
      (TM2StackFrame.embed (copyLayout false) (copyPresent (some false) (uniformNatEncode e) [] [])
        ![q.bits,[],[],[],[]]) = state (some (copyLabel false 0)) q.bits (uniformNatEncode e) [] [] [] := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have hct : TM2ReturnLink.embed (copyLabel false) (if false then subLabel 0 else parseLabel 0)
      (TM2StackFrame.embed (copyLayout false) (copyPresent none (uniformNatEncode e) (uniformNatEncode e) [])
        ![q.bits,[],[],[],[]]) = state (some (parseLabel 0)) q.bits (uniformNatEncode e) (uniformNatEncode e) [] [] := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rw [hcs,hct] at hcopy
  obtain ⟨v,hv,hparse⟩ := parse_run e q.bits (uniformNatEncode e)
  obtain ⟨w,hw,hqcopy⟩ := copy_run true q.bits ![uniformNatEncode e,[],e.bits,[],[]]
  have hqs : TM2ReturnLink.embed (copyLabel true) (if true then subLabel 0 else parseLabel 0)
      (TM2StackFrame.embed (copyLayout true) (copyPresent (some false) q.bits [] [])
        ![uniformNatEncode e,[],e.bits,[],[]]) = state (some (copyLabel true 0)) q.bits (uniformNatEncode e) [] e.bits [] := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have hqt : TM2ReturnLink.embed (copyLabel true) (if true then subLabel 0 else parseLabel 0)
      (TM2StackFrame.embed (copyLayout true) (copyPresent none q.bits q.bits [])
        ![uniformNatEncode e,[],e.bits,[],[]]) = state (some (subLabel 0)) q.bits (uniformNatEncode e) q.bits e.bits [] := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rw [hqs,hqt] at hqcopy
  obtain ⟨x,hx,hsub⟩ := sub_run q e he (uniformNatEncode e)
  have hstart : tick (start q.bits (uniformNatEncode e)) =
      state (some (copyLabel false 0)) q.bits (uniformNatEncode e) [] [] [] := rfl
  have hparseGate : tick (state (some 1) q.bits (uniformNatEncode e) [] e.bits [] 2) =
      state (some (copyLabel true 0)) q.bits (uniformNatEncode e) [] e.bits [] := rfl
  have hfinish : tick (state (some 2) q.bits (uniformNatEncode e) [] e.bits (q-e).bits 2) =
      result q.bits (uniformNatEncode e) e.bits (q-e).bits := rfl
  refine ⟨1+(x+(w+(1+(v+(u+1))))),?_,?_⟩
  · rw [uniformNatEncode_length] at hu
    rw [Nat.size_eq_bits_len] at hw
    have hs := Nat.size_le_size (show e ≤ q-1 by omega)
    unfold clock
    omega
  · simp only [Function.iterate_add_apply,Function.iterate_one,hstart,hcopy,hparse,hparseGate,hqcopy,hsub,hfinish]

/-- Clock padding is used only after the derived final halt. -/
theorem padded_run (q e : Nat) (he : e < q) :
    tick^[clock q] (start q.bits (uniformNatEncode e)) =
      result q.bits (uniformNatEncode e) e.bits (q-e).bits := by
  obtain ⟨u,hu,hr⟩ := run q e he
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hu
  rw [hd,Nat.add_comm u d,Function.iterate_add_apply,hr]
  exact Function.iterate_fixed (by rfl) d

theorem local_cost (l : Fin 21) : BitOracleMachine.localCost (program l) ≤ 32 := by
  fin_cases l <;> decide +kernel

/-- The charged machine run follows from the actual executed complement
controller and finite instruction bound, without a supplied cost certificate. -/
theorem charged (q e : Nat) (he : e < q) :
    ∃ charge ≤ 32*clock q,
      BitOracleMachine.run code (clock q) (start q.bits (uniformNatEncode e)) =
      pure (result q.bits (uniformNatEncode e) e.bits (q-e).bits,charge) := by
  obtain ⟨c,hc,hr⟩ := BitOracleMachine.compute_run_cost program 32 local_cost (clock q)
    (start q.bits (uniformNatEncode e))
  refine ⟨c,hc,?_⟩
  change BitOracleMachine.run code (clock q) (start q.bits (uniformNatEncode e)) =
    pure (tick^[clock q] (start q.bits (uniformNatEncode e)),c) at hr
  rw [hr,padded_run q e he]

#print axioms run
#print axioms padded_run
#print axioms local_cost
#print axioms charged
end ExplainableCrypto.Helios.Computational.ScalarComplementMachine
