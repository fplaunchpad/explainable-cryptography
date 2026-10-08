import ExplainableCrypto.Helios.Computational.ScalarDifferenceMachine

namespace ExplainableCrypto.Helios.Computational.ScalarDifferenceMachine
open Turing.TM2
set_option maxRecDepth 65536

def state (phase : Option (Fin size)) (q cRecord eRecord cDigits eDigits temp answer : List Bool)
    (v : Fin 3 := 0) : Config :=
  ⟨phase,v,![q,cRecord,eRecord,answer,eDigits,temp,[],[],[],cDigits]⟩

theorem copy_code (which : Bool) (l : Fin 2) : program (copyLabel which l) =
    TM2ReturnLink.redirect (copyLabel which) (parseLabel which 0) (copyProgram which l) := by
  cases which <;> fin_cases l <;> rfl

theorem parse_code (which : Bool) (l : Fin 3) : program (parseLabel which l) =
    TM2ReturnLink.redirect (parseLabel which) (if which then 2 else 1) (parseProgram which l) := by
  cases which <;> fin_cases l <;> rfl

theorem difference_code (l : Fin 42) : program (differenceLabel l) =
    TM2ReturnLink.redirect differenceLabel 3 (differenceProgram l) := by
  fin_cases l <;> rfl

theorem writer_code (l : Fin CacheRoutineCode.writerSize) : program (writerLabel l) =
    TM2ReturnLink.redirect writerLabel 5 (writerProgram l) := by
  fin_cases l <;> rfl

theorem entry_step (q c e : List Bool) :
    tick (start q c e) = state (some (copyLabel false 0)) q c e [] [] [] [] := rfl

theorem first_parse_return (q c e cd : List Bool) :
    tick (state (some 1) q c e cd [] [] [] 2) =
      state (some (copyLabel true 0)) q c e cd [] [] [] := rfl

theorem second_parse_return (q c e cd ed : List Bool) :
    tick (state (some 2) q c e cd ed [] [] 2) =
      state (some (differenceLabel (BinaryModAddMachine.subLabel 0 0))) q c e cd ed [] [] := rfl

theorem difference_return (q c e dd ed : List Bool) :
    tick (state (some 3) q c e dd ed [] [] 2) = state (some 4) q c e dd ed [] [] := rfl

theorem clear_done (q c e dd : List Bool) (v : Fin 3) :
    tick (state (some 4) q c e dd [] [] [] v) = state (some writerEntry) q c e dd [] [] [] := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

theorem clear_bit (q c e dd ed : List Bool) (b : Bool) (v : Fin 3) :
    tick (state (some 4) q c e dd (b::ed) [] [] v) =
      state (some 4) q c e dd ed [] [] (BinaryModuloCode.memory (some b)) := by
  cases b <;> (change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩; congr 1; funext k; fin_cases k <;> rfl)

theorem writer_return (q c e answer : List Bool) :
    tick (state (some 5) q c e [] [] [] answer 2) = result q c e answer := rfl

#print axioms copy_code
#print axioms parse_code
#print axioms difference_code
#print axioms writer_code
#print axioms entry_step
#print axioms first_parse_return
#print axioms second_parse_return
#print axioms difference_return
#print axioms clear_done
#print axioms clear_bit
#print axioms writer_return
end ExplainableCrypto.Helios.Computational.ScalarDifferenceMachine

namespace ExplainableCrypto.Helios.Computational.ScalarDifferenceMachine
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

private def copyPresent (phase : Option Bool) (src dst scratch : List Bool) :=
  TM2FiniteCoordinates.present PrimeNonceCiphertextMachine.copyPorts
    PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory
    (BitCopyMachine.config phase src dst scratch)

private theorem copy_run (which : Bool) (word : List Bool) (frame : Fin 7 → List Bool) :
    ∃ used ≤ 2*word.length+2,
      tick^[used]
        (TM2ReturnLink.embed (copyLabel which) (parseLabel which 0)
          (TM2StackFrame.embed (copyLayout which) (copyPresent (some false) word [] []) frame)) =
        TM2ReturnLink.embed (copyLabel which) (parseLabel which 0)
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
    (parseLabel which 0) (copy_code which) (2*word.length+2) _ (by rw [hf]; rfl)
  rw [hf] at he
  exact ⟨used,hu,he⟩

private theorem copy_phase (which : Bool) (q c e cd : List Bool) :
    ∃ used ≤ 2*(if which then e else c).length+2,
      tick^[used] (state (some (copyLabel which 0)) q c e cd [] [] []) =
      state (some (parseLabel which 0)) q c e cd [] (if which then e else c) [] := by
  let frame : Fin 7 → List Bool := if which then ![q,c,[],[],[],[],cd] else ![q,e,[],[],[],[],cd]
  obtain ⟨u,hu,hr⟩ := copy_run which (if which then e else c) frame
  refine ⟨u,hu,?_⟩
  have hs : TM2ReturnLink.embed (copyLabel which) (parseLabel which 0)
      (TM2StackFrame.embed (copyLayout which) (copyPresent (some false) (if which then e else c) [] []) frame) =
      state (some (copyLabel which 0)) q c e cd [] [] [] := by
    cases which <;> (change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩; congr 1; funext k; fin_cases k <;> rfl)
  have he : TM2ReturnLink.embed (copyLabel which) (parseLabel which 0)
      (TM2StackFrame.embed (copyLayout which) (copyPresent none (if which then e else c) (if which then e else c) []) frame) =
      state (some (parseLabel which 0)) q c e cd [] (if which then e else c) [] := by
    cases which <;> (change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩; congr 1; funext k; fin_cases k <;> rfl)
  rwa [hs,he] at hr

private theorem parse_phase (which : Bool) (n : Nat) (q c e cd : List Bool)
    (hcd : which = false → cd = []) :
    ∃ used ≤ 3*n.size+3,
      tick^[used] (state (some (parseLabel which 0)) q c e cd [] (uniformNatEncode n) []) =
      state (some (if which then 2 else 1)) q c e (if which then cd else n.bits)
        (if which then n.bits else []) [] [] 2 := by
  let initial := TM2FiniteCoordinates.present PrimeNonceCiphertextMachine.parsePorts
    PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory
    (NatPrefixMachine.start (uniformNatEncode n))
  let final := TM2FiniteCoordinates.present PrimeNonceCiphertextMachine.parsePorts
    PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory
    (NatPrefixMachine.config none [] [] [] n.bits (some true))
  let frame : Fin 6 → List Bool := if which then ![q,c,e,[],[],cd] else ![q,c,e,[],[],[]]
  have hi : (TM2ReturnLink.tick
      (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.parsePorts
        PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory NatPrefixMachine.program))^[3*n.size+3]
      initial = final := by
    dsimp only [initial]
    rw [TM2FiniteCoordinates.run]
    have h := NatPrefixMachine.encoded_run n []
    simp only [List.append_nil] at h
    change (TM2ReturnLink.tick NatPrefixMachine.program)^[3*n.size+3] _ = _ at h
    rw [h]
  have hf := TM2StackFrame.run (parseLayout which)
    (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.parsePorts
      PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory NatPrefixMachine.program)
    (3*n.size+3) initial frame
  rw [hi] at hf
  change (TM2ReturnLink.tick (parseProgram which))^[3*n.size+3]
    (TM2StackFrame.embed (parseLayout which) initial frame) =
    TM2StackFrame.embed (parseLayout which) final frame at hf
  obtain ⟨u,hu,hr⟩ := TM2ReturnLink.run (parseProgram which) program (parseLabel which)
    (if which then 2 else 1) (parse_code which) (3*n.size+3) _ (by rw [hf]; rfl)
  rw [hf] at hr
  have hs : TM2ReturnLink.embed (parseLabel which) (if which then 2 else 1)
      (TM2StackFrame.embed (parseLayout which) initial frame) =
      state (some (parseLabel which 0)) q c e cd [] (uniformNatEncode n) [] := by
    cases which
    · have hd := hcd rfl; subst cd
      change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩; congr 1; funext k; fin_cases k <;> rfl
    · change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩; congr 1; funext k; fin_cases k <;> rfl
  have he : TM2ReturnLink.embed (parseLabel which) (if which then 2 else 1)
      (TM2StackFrame.embed (parseLayout which) final frame) =
      state (some (if which then 2 else 1)) q c e (if which then cd else n.bits)
        (if which then n.bits else []) [] [] 2 := by
    cases which <;> (change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩; congr 1; funext k; fin_cases k <;> rfl)
  exact ⟨u,hu,by rwa [hs,he] at hr⟩

private theorem difference_phase (q c e : Nat) (hc : c < q) (he : e < q)
    (cr er : List Bool) :
    ∃ used ≤ BinaryModAddMachine.clock q,
      tick^[used] (state (some (differenceLabel (BinaryModAddMachine.subLabel 0 0)))
        q.bits cr er c.bits e.bits [] []) =
      state (some 3) q.bits cr er ((c+q-e)%q).bits e.bits [] [] 2 := by
  let frame : Fin 2 → List Bool := ![cr,er]
  have hf := TM2StackFrame.run differenceLayout BinaryModAddMachine.program
    (BinaryModAddMachine.clock q) (BinaryModAddMachine.start c.bits e.bits q.bits) frame
  change (TM2ReturnLink.tick differenceProgram)^[BinaryModAddMachine.clock q]
    (TM2StackFrame.embed differenceLayout (BinaryModAddMachine.start c.bits e.bits q.bits) frame) = _ at hf
  change _ = TM2StackFrame.embed differenceLayout
    (BinaryModAddMachine.tick^[BinaryModAddMachine.clock q] (BinaryModAddMachine.start c.bits e.bits q.bits)) frame at hf
  rw [BinaryModAddMachine.difference_run q c e hc he] at hf
  obtain ⟨u,hu,hr⟩ := TM2ReturnLink.run differenceProgram program differenceLabel 3 difference_code
    (BinaryModAddMachine.clock q) _ (by rw [hf]; rfl)
  rw [hf] at hr
  have hs : TM2ReturnLink.embed differenceLabel 3
      (TM2StackFrame.embed differenceLayout (BinaryModAddMachine.start c.bits e.bits q.bits) frame) =
      state (some (differenceLabel (BinaryModAddMachine.subLabel 0 0))) q.bits cr er c.bits e.bits [] [] := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩; congr 1; funext k; fin_cases k <;> rfl
  have ht : TM2ReturnLink.embed differenceLabel 3
      (TM2StackFrame.embed differenceLayout (BinaryModAddMachine.result ((c+q-e)%q).bits e.bits q.bits) frame) =
      state (some 3) q.bits cr er ((c+q-e)%q).bits e.bits [] [] 2 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩; congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu,by rwa [hs,ht] at hr⟩

private theorem clear_run (q c e dd ed : List Bool) (v : Fin 3) :
    tick^[ed.length+1] (state (some 4) q c e dd ed [] [] v) =
      state (some writerEntry) q c e dd [] [] [] := by
  induction ed generalizing v with
  | nil => simpa using clear_done q c e dd v
  | cons b ed ih => rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply,clear_bit,ih]

#print axioms copy_phase
#print axioms parse_phase
#print axioms difference_phase
#print axioms clear_run
end ExplainableCrypto.Helios.Computational.ScalarDifferenceMachine

namespace ExplainableCrypto.Helios.Computational.ScalarDifferenceMachine
open Turing.TM2
set_option maxRecDepth 65536

private def writerPresent (cfg : FrameWriteMachine.Config) (frame : Fin 5 → List Bool) :=
  TM2StackFrame.embed writerLayout
    (TM2FiniteCoordinates.present writerPorts CacheRoutineCode.writerLabels
      BinaryModuloCode.memory cfg) frame

/-- The existing scalar writer consumes the actual difference digits and
preserves both original prefixes and the modulus through a live return. -/
theorem writer_phase (d : Nat) (q cRecord eRecord : List Bool) :
    ∃ used ≤ 3*d.size+3,
      tick^[used] (state (some writerEntry) q cRecord eRecord d.bits [] [] []) =
        state (some 5) q cRecord eRecord [] [] [] (uniformNatEncode d) 2 := by
  have he := FrameWriteMachine.prefix_run d [] none
  change (TM2ReturnLink.tick FrameWriteMachine.program)^[3*d.size+3]
    (FrameWriteMachine.state (some .digits) [] [] [] [] d.bits none) =
    FrameWriteMachine.state none [] [] [] (uniformNatEncode d++[]) [] (some true) at he
  simp only [List.append_nil] at he
  have hc : (TM2ReturnLink.tick writerProgram)^[3*d.size+3]
      (writerPresent (FrameWriteMachine.state (some .digits) [] [] [] [] d.bits none)
        ![q,cRecord,eRecord,[],[]]) =
      writerPresent (FrameWriteMachine.state none [] [] [] (uniformNatEncode d) [] (some true))
        ![q,cRecord,eRecord,[],[]] := by
    unfold writerProgram writerPresent
    rw [TM2StackFrame.run,TM2FiniteCoordinates.run,he]
  obtain ⟨u,hu,hr⟩ := TM2ReturnLink.run writerProgram program writerLabel 5 writer_code
    (3*d.size+3) _ (by rw [hc]; rfl)
  rw [hc] at hr
  have hi : TM2ReturnLink.embed writerLabel 5
      (writerPresent (FrameWriteMachine.state (some .digits) [] [] [] [] d.bits none)
        ![q,cRecord,eRecord,[],[]]) =
      state (some writerEntry) q cRecord eRecord d.bits [] [] [] := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    funext k
    fin_cases k <;> rfl
  have ho : TM2ReturnLink.embed writerLabel 5
      (writerPresent (FrameWriteMachine.state none [] [] [] (uniformNatEncode d) [] (some true))
        ![q,cRecord,eRecord,[],[]]) =
      state (some 5) q cRecord eRecord [] [] [] (uniformNatEncode d) 2 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [hi,ho] at hr
  exact ⟨u,hu,hr⟩

#print axioms writer_phase
end ExplainableCrypto.Helios.Computational.ScalarDifferenceMachine

namespace ExplainableCrypto.Helios.Computational.ScalarDifferenceMachine
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-- Both scalar prefixes are copied and parsed, modular subtraction executes,
and the canonical output prefix is written with all temporary words cleared. -/
theorem run (q c e : Nat) (hc : c < q) (he : e < q) :
    ∃ used ≤ clock q,
      tick^[used] (start q.bits (uniformNatEncode c) (uniformNatEncode e)) =
        result q.bits (uniformNatEncode c) (uniformNatEncode e) (uniformNatEncode ((c+q-e)%q)) := by
  obtain ⟨u,hu,hcopyC⟩ := copy_phase false q.bits (uniformNatEncode c) (uniformNatEncode e) []
  obtain ⟨v,hv,hparseC⟩ := parse_phase false c q.bits (uniformNatEncode c) (uniformNatEncode e) [] (by intro _; rfl)
  obtain ⟨w,hw,hcopyE⟩ := copy_phase true q.bits (uniformNatEncode c) (uniformNatEncode e) c.bits
  obtain ⟨x,hx,hparseE⟩ := parse_phase true e q.bits (uniformNatEncode c) (uniformNatEncode e) c.bits (by intro h; cases h)
  obtain ⟨y,hy,hdiff⟩ := difference_phase q c e hc he (uniformNatEncode c) (uniformNatEncode e)
  obtain ⟨z,hz,hwrite⟩ := writer_phase ((c+q-e)%q) q.bits (uniformNatEncode c) (uniformNatEncode e)
  have hclear := clear_run q.bits (uniformNatEncode c) (uniformNatEncode e) ((c+q-e)%q).bits e.bits 0
  simp only [Bool.false_eq_true,ite_false,ite_true] at hu hcopyC hv hparseC hw hcopyE hx hparseE
  generalize ht : e.bits.length+1 = t at hclear
  refine ⟨1+(z+(t+(1+(y+(1+(x+(w+(1+(v+(u+1)))))))))),?_,?_⟩
  · rw [uniformNatEncode_length] at hu hw
    have hcsize := Nat.size_le_size (show c ≤ q-1 by omega)
    have hesize := Nat.size_le_size (show e ≤ q-1 by omega)
    have hd : (c+q-e)%q < q := Nat.mod_lt _ (by omega)
    have hdsize := Nat.size_le_size (show (c+q-e)%q ≤ q-1 by omega)
    rw [Nat.size_eq_bits_len] at ht
    simp only [←Nat.add_assoc]
    dsimp only [clock,BinaryModAddMachine.clock] at *
    omega
  · simp only [Function.iterate_add_apply,Function.iterate_one,entry_step,hcopyC,hparseC,
      first_parse_return,hcopyE,hparseE,second_parse_return,hdiff,difference_return,hclear,hwrite,writer_return]

/-- Padding starts only after the concrete derived halt. -/
theorem padded_run (q c e : Nat) (hc : c < q) (he : e < q) :
    tick^[clock q] (start q.bits (uniformNatEncode c) (uniformNatEncode e)) =
      result q.bits (uniformNatEncode c) (uniformNatEncode e) (uniformNatEncode ((c+q-e)%q)) := by
  obtain ⟨u,hu,hr⟩ := run q c e hc he
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hu
  rw [hd,Nat.add_comm u d,Function.iterate_add_apply,hr]
  exact Function.iterate_fixed (by rfl) d

theorem local_cost (l : Fin size) : BitOracleMachine.localCost (program l) ≤ 32 := by
  fin_cases l <;> decide +kernel

/-- The total charge is derived from the actual controller's execution and
finite instruction costs, with no assumed operand or execution certificate. -/
theorem charged (q c e : Nat) (hc : c < q) (he : e < q) :
    ∃ charge ≤ cost q,
      BitOracleMachine.run code (clock q) (start q.bits (uniformNatEncode c) (uniformNatEncode e)) =
      pure (result q.bits (uniformNatEncode c) (uniformNatEncode e) (uniformNatEncode ((c+q-e)%q)),charge) := by
  obtain ⟨charge,hcost,hr⟩ := BitOracleMachine.compute_run_cost program 32 local_cost (clock q)
    (start q.bits (uniformNatEncode c) (uniformNatEncode e))
  refine ⟨charge,hcost,?_⟩
  change BitOracleMachine.run code (clock q) (start q.bits (uniformNatEncode c) (uniformNatEncode e)) =
    pure (tick^[clock q] (start q.bits (uniformNatEncode c) (uniformNatEncode e)),charge) at hr
  rw [hr,padded_run q c e hc he]

private theorem scalar_difference_value {q : Nat} [NeZero q] (c e : ZMod q) :
    (c-e).val = (c.val+q-e.val)%q := by
  have he : e.val ≤ c.val+q := by have := ZMod.val_lt e; omega
  have hcast : ((c.val+q-e.val : Nat) : ZMod q) = c-e := by
    rw [Nat.cast_sub he]
    simp
  rw [←hcast,ZMod.val_natCast]

/-- Typed full-field scalars provide all numeric bounds and the scalar result.
The enclosing caller still must derive the actual prefix/frame origins. -/
theorem charged_source {q : Nat} [NeZero q] (c e : ZMod q) :
    ∃ charge ≤ cost q,
      BitOracleMachine.run code (clock q) (start q.bits (uniformNatEncode c.val) (uniformNatEncode e.val)) =
      pure (result q.bits (uniformNatEncode c.val) (uniformNatEncode e.val) (uniformNatEncode (c-e).val),charge) := by
  rw [scalar_difference_value]
  exact charged q c.val e.val (ZMod.val_lt _) (ZMod.val_lt _)

#print axioms run
#print axioms padded_run
#print axioms local_cost
#print axioms charged
#print axioms charged_source
end ExplainableCrypto.Helios.Computational.ScalarDifferenceMachine
