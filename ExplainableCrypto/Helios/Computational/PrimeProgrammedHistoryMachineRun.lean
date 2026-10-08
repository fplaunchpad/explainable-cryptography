import ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine
import ExplainableCrypto.Helios.Computational.NatFieldWriterMachineRun
namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
/-- Only live words changed between the fixed stages; all other old words are framed. -/
def words (old : Fin 48 → List Bool) (pair stmt history : List Bool) : Fin 48 → List Bool :=
  Function.update (Function.update (Function.update old 28 pair) 29 stmt) 47 history
def state (phase : Option (Fin size)) (memory : Fin 3)
    (old : Fin 48 → List Bool) (pair stmt history : List Bool) : Config :=
  ⟨phase,memory,words old pair stmt history⟩
end ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem nat_code (which : Fin 4) (l : Fin 21) :
    program (natLabel which l) = TM2ReturnLink.redirect (natLabel which) (natReturn which)
      (natProgram which l) := by
  have hv := which.isLt
  have hl := l.isLt
  have h0 : natLabel which l ≠ 0 := by intro he; have he' := congrArg Fin.val he; change 9+21*which.val+l.val = 0 at he'; omega
  have h1 : natLabel which l ≠ 1 := by intro he; have he' := congrArg Fin.val he; change 9+21*which.val+l.val = 1 at he'; omega
  have h2 : natLabel which l ≠ 2 := by intro he; have he' := congrArg Fin.val he; change 9+21*which.val+l.val = 2 at he'; omega
  have h3 : natLabel which l ≠ 3 := by intro he; have he' := congrArg Fin.val he; change 9+21*which.val+l.val = 3 at he'; omega
  have h4 : natLabel which l ≠ 4 := by intro he; have he' := congrArg Fin.val he; change 9+21*which.val+l.val = 4 at he'; omega
  have h5 : natLabel which l ≠ 5 := by intro he; have he' := congrArg Fin.val he; change 9+21*which.val+l.val = 5 at he'; omega
  have h6 : natLabel which l ≠ 6 := by intro he; have he' := congrArg Fin.val he; change 9+21*which.val+l.val = 6 at he'; omega
  have h7 : natLabel which l ≠ 7 := by intro he; have he' := congrArg Fin.val he; change 9+21*which.val+l.val = 7 at he'; omega
  have h8 : natLabel which l ≠ 8 := by intro he; have he' := congrArg Fin.val he; change 9+21*which.val+l.val = 8 at he'; omega
  have h : (natLabel which l).val < 93 := by dsimp [natLabel]; omega
  have hd : ((natLabel which l).val-9)/21 = which.val := by dsimp [natLabel]; omega
  have hm : ((natLabel which l).val-9)%21 = l.val := by dsimp [natLabel]; omega
  simp only [program,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,
    if_neg h5,if_neg h6,if_neg h7,if_neg h8,dif_pos h,hd,hm]

def natFrame (which : Fin 4) (old : Fin 48 → List Bool) (stmt history : List Bool) :
    Fin 41 → List Bool := fun j => words old [] stmt history (natLayout which (.inr j))

private theorem nat_output (which : Fin 4) : natLayout which (.inl 1) = 28 := by
  fin_cases which <;> rfl

private theorem nat_local (which : Fin 4) (old : Fin 48 → List Bool)
    (pair stmt history : List Bool) (hw : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = [])
    (j : Fin 7) :
    words old pair stmt history (natLayout which (.inl j)) =
      ![old (sourcePort which),pair,[],[],[],[],[]] j := by
  have h0:=hw 0; have h1:=hw 1; have h2:=hw 2; have h3:=hw 3; have h4:=hw 4
  fin_cases which <;> fin_cases j <;>
    first | rfl | exact h0 | exact h1 | exact h2 | exact h3 | exact h4

private theorem words_pair_irrel (old : Fin 48 → List Bool) (a b stmt history : List Bool)
    (k : Fin 48) (hk : k ≠ 28) : words old a stmt history k = words old b stmt history k := by
  simp [words,Function.update_apply,hk]

private theorem nat_data (which : Fin 4) (old : Fin 48 → List Bool)
    (pair stmt history : List Bool) (hw : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = []) :
    TM2StackFrame.data (natLayout which) ![old (sourcePort which),pair,[],[],[],[],[]]
      (natFrame which old stmt history) = words old pair stmt history := by
  funext k
  obtain ⟨k,rfl⟩ := (natLayout which).surjective k
  cases k with
  | inl j => simpa only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl] using
      (nat_local which old pair stmt history hw j).symm
  | inr j =>
    have hn : natLayout which (.inr j) ≠ 28 := by
      rw [←nat_output which]; intro h; have he := (natLayout which).injective h; cases he
    simpa only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inr,natFrame] using
      words_pair_irrel old [] pair stmt history _ hn

theorem nat_run (which : Fin 4) (n : Nat) (old : Fin 48 → List Bool)
    (pair stmt history : List Bool) (hw : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = [])
    (hn : old (sourcePort which)=n.bits) :
    ∃ used ≤ NatFieldWriterMachine.clock n,
      tick^[used] (state (some (natLabel which 0)) 2 old pair stmt history) =
        state (some (natReturn which)) 2 old (NatFieldWriterMachine.encoded n pair) stmt history := by
  have he := TM2StackFrame.run (natLayout which) NatFieldWriterMachine.program
    (NatFieldWriterMachine.clock n) (NatFieldWriterMachine.start n.bits pair)
    (natFrame which old stmt history)
  change (TM2ReturnLink.tick (natProgram which))^[_] _ =
    TM2StackFrame.embed (natLayout which) (NatFieldWriterMachine.tick^[_] _)
      (natFrame which old stmt history) at he
  rw [NatFieldWriterMachine.padded_run] at he
  have hh : ((TM2ReturnLink.tick (natProgram which))^[NatFieldWriterMachine.clock n]
      (TM2StackFrame.embed (natLayout which) (NatFieldWriterMachine.start n.bits pair)
        (natFrame which old stmt history))).l = none := by rw [he]; rfl
  obtain ⟨used,hu,hr⟩ := TM2ReturnLink.run (natProgram which) program
    (natLabel which) (natReturn which) (nat_code which) _ _ hh
  rw [he] at hr
  have hi : TM2ReturnLink.embed (natLabel which) (natReturn which)
      (TM2StackFrame.embed (natLayout which) (NatFieldWriterMachine.start n.bits pair)
        (natFrame which old stmt history)) = state (some (natLabel which 0)) 2 old pair stmt history := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    rw [←hn]
    exact nat_data which old pair stmt history hw
  have ho : TM2ReturnLink.embed (natLabel which) (natReturn which)
      (TM2StackFrame.embed (natLayout which)
        (NatFieldWriterMachine.result n.bits (NatFieldWriterMachine.encoded n pair))
        (natFrame which old stmt history)) =
      state (some (natReturn which)) 2 old (NatFieldWriterMachine.encoded n pair) stmt history := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    rw [←hn]
    exact nat_data which old _ stmt history hw
  rw [hi,ho] at hr
  exact ⟨used,hu,hr⟩
#print axioms nat_run
end ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
private theorem writer_code (which : Fin 4) (l : Fin 8) :
    program (writerLabel which l) = TM2ReturnLink.redirect (writerLabel which) (writerReturn which)
      (writerProgram which l) := by
  have hv := which.isLt
  have hl := l.isLt
  have h0 : writerLabel which l ≠ 0 := by intro he; have he' := congrArg Fin.val he; change 93+8*which.val+l.val = 0 at he'; omega
  have h1 : writerLabel which l ≠ 1 := by intro he; have he' := congrArg Fin.val he; change 93+8*which.val+l.val = 1 at he'; omega
  have h2 : writerLabel which l ≠ 2 := by intro he; have he' := congrArg Fin.val he; change 93+8*which.val+l.val = 2 at he'; omega
  have h3 : writerLabel which l ≠ 3 := by intro he; have he' := congrArg Fin.val he; change 93+8*which.val+l.val = 3 at he'; omega
  have h4 : writerLabel which l ≠ 4 := by intro he; have he' := congrArg Fin.val he; change 93+8*which.val+l.val = 4 at he'; omega
  have h5 : writerLabel which l ≠ 5 := by intro he; have he' := congrArg Fin.val he; change 93+8*which.val+l.val = 5 at he'; omega
  have h6 : writerLabel which l ≠ 6 := by intro he; have he' := congrArg Fin.val he; change 93+8*which.val+l.val = 6 at he'; omega
  have h7 : writerLabel which l ≠ 7 := by intro he; have he' := congrArg Fin.val he; change 93+8*which.val+l.val = 7 at he'; omega
  have h8 : writerLabel which l ≠ 8 := by intro he; have he' := congrArg Fin.val he; change 93+8*which.val+l.val = 8 at he'; omega
  have ha : ¬ (writerLabel which l).val < 93 := by dsimp [writerLabel]; omega
  have hb : (writerLabel which l).val < 125 := by dsimp [writerLabel]; omega
  have hd : ((writerLabel which l).val-93)/8 = which.val := by dsimp [writerLabel]; omega
  have hm : ((writerLabel which l).val-93)%8 = l.val := by dsimp [writerLabel]; omega
  simp only [program,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,
    if_neg h5,if_neg h6,if_neg h7,if_neg h8,dif_neg ha,dif_pos hb,hd,hm]
private def writerPresent (which : Fin 4) (cfg : FrameWriteMachine.Config)
    (frame : Fin 43 → List Bool) :=
  TM2StackFrame.embed (writerLayout which)
    (TM2FiniteCoordinates.present ScalarDifferenceMachine.writerPorts CacheRoutineCode.writerLabels
      BinaryModuloCode.memory cfg) frame
private def writerFrame (which : Fin 4) (old : Fin 48 → List Bool) (pair stmt history : List Bool) :=
  fun j : Fin 43 => words old pair stmt history (writerLayout which (.inr j))
def fieldWord (payload suffix : List Bool) := uniformNatEncode payload.length++(payload++suffix)
def fieldAfter (which : Fin 3) (old : Fin 48 → List Bool) (pair stmt history : List Bool) : Config :=
  if which.val < 2 then state (some (writerReturn which.castSucc)) 2 old [] (fieldWord pair stmt) history
  else state (some (writerReturn which.castSucc)) 2 old pair [] (fieldWord stmt history)

theorem field_run (which : Fin 3) (old : Fin 48 → List Bool) (pair stmt history : List Bool)
    (hw : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = []) :
    ∃ used ≤ FrameWriteMachine.cost (if which.val < 2 then pair.length else stmt.length),
      tick^[used] (state (some (writerLabel which.castSucc 3)) 0 old pair stmt history) =
        fieldAfter which old pair stmt history := by
  let payload := if which.val < 2 then pair else stmt
  let suffix := if which.val < 2 then stmt else history
  obtain ⟨fuel,hf,he⟩ := FrameWriteMachine.run payload suffix
  change (TM2ReturnLink.tick FrameWriteMachine.program)^[fuel] _ = _ at he
  have hc : (TM2ReturnLink.tick (writerProgram which.castSucc))^[fuel]
      (writerPresent which.castSucc (FrameWriteMachine.start payload suffix)
        (writerFrame which.castSucc old pair stmt history)) =
      writerPresent which.castSucc
        (FrameWriteMachine.state none [] [] [] (fieldWord payload suffix) [] (some true))
        (writerFrame which.castSucc old pair stmt history) := by
    have hx := TM2FiniteCoordinates.run ScalarDifferenceMachine.writerPorts
      CacheRoutineCode.writerLabels BinaryModuloCode.memory FrameWriteMachine.program fuel
      (FrameWriteMachine.start payload suffix)
    rw [he] at hx
    have hy := TM2StackFrame.run (writerLayout which.castSucc)
      (TM2FiniteCoordinates.program ScalarDifferenceMachine.writerPorts CacheRoutineCode.writerLabels
        BinaryModuloCode.memory FrameWriteMachine.program) fuel
      (TM2FiniteCoordinates.present ScalarDifferenceMachine.writerPorts CacheRoutineCode.writerLabels
        BinaryModuloCode.memory (FrameWriteMachine.start payload suffix))
      (writerFrame which.castSucc old pair stmt history)
    rw [hx] at hy
    exact hy
  obtain ⟨u,hu,hr⟩ := TM2ReturnLink.run (writerProgram which.castSucc) program
    (writerLabel which.castSucc) (writerReturn which.castSucc) (writer_code which.castSucc)
    fuel (writerPresent which.castSucc (FrameWriteMachine.start payload suffix)
      (writerFrame which.castSucc old pair stmt history)) (by rw [hc]; rfl)
  rw [hc] at hr
  have h0:=hw 0; have h1:=hw 1; have h2:=hw 2
  have hi : TM2ReturnLink.embed (writerLabel which.castSucc) (writerReturn which.castSucc)
      (writerPresent which.castSucc (FrameWriteMachine.start payload suffix)
        (writerFrame which.castSucc old pair stmt history)) =
      state (some (writerLabel which.castSucc 3)) 0 old pair stmt history := by
    fin_cases which <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩ <;> congr 1 <;>
      funext k <;> fin_cases k <;>
      first | rfl | exact h0.symm | exact h1.symm | exact h2.symm
  have ho : TM2ReturnLink.embed (writerLabel which.castSucc) (writerReturn which.castSucc)
      (writerPresent which.castSucc
        (FrameWriteMachine.state none [] [] [] (fieldWord payload suffix) [] (some true))
        (writerFrame which.castSucc old pair stmt history)) = fieldAfter which old pair stmt history := by
    fin_cases which <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩ <;> congr 1 <;>
      funext k <;> fin_cases k <;>
      first | rfl | exact h0.symm | exact h1.symm | exact h2.symm
  rw [hi,ho] at hr
  refine ⟨u,hu.trans ?_,hr⟩
  simpa only [payload,apply_ite List.length] using hf
#print axioms field_run
end ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

private theorem parse_code (l : Fin 3) : program (parseLabel l) =
    TM2ReturnLink.redirect parseLabel 5 (parseProgram l) := by
  fin_cases l <;> rfl
private theorem increment_code (l : Fin 2) : program (incrementLabel l) =
    TM2ReturnLink.redirect incrementLabel 6 (incrementProgram l) := by
  fin_cases l <;> rfl
private theorem prefix_writer_code (l : Fin 8) : program (writerLabel 3 l) =
    TM2ReturnLink.redirect (writerLabel 3) 8 (writerProgram 3 l) := by
  fin_cases l <;> rfl

/-- Parse the actual count prefix, retaining the opaque history body and statement. -/
theorem parse_history_run (h : Nat) (stmt body : List Bool) (old : Fin 48 → List Bool)
    (hwork : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = []) :
    ∃ u ≤ 3*h.size+3,
      tick^[u] (state (some (parseLabel 0)) 0 old [] stmt (uniformNatEncode h++body)) =
        state (some 5) 2 old h.bits stmt body := by
  let ports := PrimeNonceCiphertextMachine.parsePorts
  let labels := PrimeNonceCiphertextMachine.parseLabels
  let initial := TM2FiniteCoordinates.present ports labels BinaryModuloCode.memory
    (NatPrefixMachine.start (uniformNatEncode h++body))
  let final := TM2FiniteCoordinates.present ports labels BinaryModuloCode.memory
    (NatPrefixMachine.config none body [] [] h.bits (some true))
  let frame : Fin 44 → List Bool := fun j => (words old [] stmt body) (parseLayout (.inr j))
  have hi : (TM2ReturnLink.tick
      (TM2FiniteCoordinates.program ports labels BinaryModuloCode.memory NatPrefixMachine.program))^[3*h.size+3]
      initial = final := by
    dsimp only [initial]
    rw [TM2FiniteCoordinates.run]
    rw [show (TM2ReturnLink.tick NatPrefixMachine.program)^[3*h.size+3]
      (NatPrefixMachine.start (uniformNatEncode h++body)) =
      NatPrefixMachine.config none body [] [] h.bits (some true) from NatPrefixMachine.encoded_run h body]
  have hf := TM2StackFrame.run parseLayout
    (TM2FiniteCoordinates.program ports labels BinaryModuloCode.memory NatPrefixMachine.program)
    (3*h.size+3) initial frame
  rw [hi] at hf
  change (TM2ReturnLink.tick parseProgram)^[3*h.size+3]
    (TM2StackFrame.embed parseLayout initial frame) = TM2StackFrame.embed parseLayout final frame at hf
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run parseProgram program parseLabel 5 parse_code
    (3*h.size+3) _ (by rw [hf]; rfl)
  rw [hf] at he
  have hs : TM2ReturnLink.embed parseLabel 5 (TM2StackFrame.embed parseLayout initial frame) =
      state (some (parseLabel 0)) 0 old [] stmt (uniformNatEncode h++body) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    fin_cases k <;> first | rfl | exact (hwork 0).symm | exact (hwork 1).symm
  have ht : TM2ReturnLink.embed parseLabel 5 (TM2StackFrame.embed parseLayout final frame) =
      state (some 5) 2 old h.bits stmt body := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    fin_cases k <;> first | rfl | exact (hwork 0).symm | exact (hwork 1).symm
  refine ⟨u,hu,?_⟩
  change (TM2ReturnLink.tick program)^[u] _ = _
  rw [hs] at he
  exact he.trans ht

/-- Carry propagation changes only the parsed count, preserving body and statement. -/
theorem increment_history_run (n : Nat) (stmt body : List Bool) (old : Fin 48 → List Bool)
    (hwork : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = []) :
    ∃ u ≤ 2*n.size+2,
      tick^[u] (state (some (incrementLabel 0)) 0 old n.bits stmt body) =
        state (some 6) 2 old (n+1).bits stmt body := by
  let ports := PrimeNonceCiphertextMachine.parsePorts
  let labels := NatFieldWriterMachine.copyLabels
  let initial := TM2FiniteCoordinates.present ports labels BinaryModuloCode.memory
    (BitIncrementMachine.config (some false) n.bits [] body [] none)
  let final := TM2FiniteCoordinates.present ports labels BinaryModuloCode.memory
    (BitIncrementMachine.config none (n+1).bits [] body [] (some true))
  let frame : Fin 44 → List Bool := fun j => (words old [] stmt body) (parseLayout (.inr j))
  obtain ⟨fuel,hfuel,hinc⟩ := BitIncrementMachine.run n body [] none
  change (TM2ReturnLink.tick BitIncrementMachine.program)^[fuel]
    (BitIncrementMachine.config (some false) n.bits [] body [] none) =
      BitIncrementMachine.config none (n+1).bits [] body [] (some true) at hinc
  have hi : (TM2ReturnLink.tick
      (TM2FiniteCoordinates.program ports labels BinaryModuloCode.memory BitIncrementMachine.program))^[fuel]
      initial = final := by
    dsimp only [initial]
    rw [TM2FiniteCoordinates.run]
    change TM2FiniteCoordinates.present ports labels BinaryModuloCode.memory
      ((TM2ReturnLink.tick BitIncrementMachine.program)^[fuel] _) = _
    rw [hinc]
  have hf := TM2StackFrame.run parseLayout
    (TM2FiniteCoordinates.program ports labels BinaryModuloCode.memory BitIncrementMachine.program)
    fuel initial frame
  rw [hi] at hf
  change (TM2ReturnLink.tick incrementProgram)^[fuel]
    (TM2StackFrame.embed parseLayout initial frame) = TM2StackFrame.embed parseLayout final frame at hf
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run incrementProgram program incrementLabel 6 increment_code
    fuel _ (by rw [hf]; rfl)
  rw [hf] at he
  have hs : TM2ReturnLink.embed incrementLabel 6 (TM2StackFrame.embed parseLayout initial frame) =
      state (some (incrementLabel 0)) 0 old n.bits stmt body := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    fin_cases k <;> first | rfl | exact (hwork 0).symm | exact (hwork 1).symm
  have ht : TM2ReturnLink.embed incrementLabel 6 (TM2StackFrame.embed parseLayout final frame) =
      state (some 6) 2 old (n+1).bits stmt body := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    fin_cases k <;> first | rfl | exact (hwork 0).symm | exact (hwork 1).symm
  refine ⟨u,hu.trans hfuel,?_⟩
  change (TM2ReturnLink.tick program)^[u] _ = _
  rw [hs] at he
  exact he.trans ht

/-- Prefix the incremented canonical count and consume its digits, retaining frame. -/
theorem prefix_history_run (n : Nat) (stmt suffix : List Bool) (old : Fin 48 → List Bool)
    (hwork : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = []) :
    ∃ u ≤ 3*n.size+3,
      tick^[u] (state (some (writerLabel 3 5)) 0 old n.bits stmt suffix) =
        state (some 8) 2 old [] stmt (uniformNatEncode n++suffix) := by
  let ports := ScalarDifferenceMachine.writerPorts
  let labels := CacheRoutineCode.writerLabels
  let initial := TM2FiniteCoordinates.present ports labels BinaryModuloCode.memory
    (FrameWriteMachine.state (some .digits) [] [] [] suffix n.bits none)
  let final := TM2FiniteCoordinates.present ports labels BinaryModuloCode.memory
    (FrameWriteMachine.state none [] [] [] (uniformNatEncode n++suffix) [] (some true))
  let frame : Fin 43 → List Bool := fun j => (words old [] stmt suffix) (prefixLayout (.inr j))
  have hi : (TM2ReturnLink.tick
      (TM2FiniteCoordinates.program ports labels BinaryModuloCode.memory FrameWriteMachine.program))^[3*n.size+3]
      initial = final := by
    dsimp only [initial]
    rw [TM2FiniteCoordinates.run]
    rw [show (TM2ReturnLink.tick FrameWriteMachine.program)^[3*n.size+3]
      (FrameWriteMachine.state (some .digits) [] [] [] suffix n.bits none) =
      FrameWriteMachine.state none [] [] [] (uniformNatEncode n++suffix) [] (some true)
      from FrameWriteMachine.prefix_run n suffix none]
  have hf := TM2StackFrame.run (writerLayout 3)
    (TM2FiniteCoordinates.program ports labels BinaryModuloCode.memory FrameWriteMachine.program)
    (3*n.size+3) initial frame
  rw [hi] at hf
  change (TM2ReturnLink.tick (writerProgram 3))^[3*n.size+3]
    (TM2StackFrame.embed prefixLayout initial frame) = TM2StackFrame.embed prefixLayout final frame at hf
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run (writerProgram 3) program (writerLabel 3) 8
    prefix_writer_code (3*n.size+3) _ (by rw [hf]; rfl)
  rw [hf] at he
  have hs : TM2ReturnLink.embed (writerLabel 3) 8 (TM2StackFrame.embed prefixLayout initial frame) =
      state (some (writerLabel 3 5)) 0 old n.bits stmt suffix := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    fin_cases k <;> first | rfl | exact (hwork 0).symm | exact (hwork 1).symm | exact (hwork 2).symm
  have ht : TM2ReturnLink.embed (writerLabel 3) 8 (TM2StackFrame.embed prefixLayout final frame) =
      state (some 8) 2 old [] stmt (uniformNatEncode n++suffix) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    fin_cases k <;> first | rfl | exact (hwork 0).symm | exact (hwork 1).symm | exact (hwork 2).symm
  refine ⟨u,hu,?_⟩
  change (TM2ReturnLink.tick program)^[u] _ = _
  rw [hs] at he
  exact he.trans ht

#print axioms parse_history_run
#print axioms increment_history_run
#print axioms prefix_history_run
end ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine
private theorem pair_length_bound (a b : List Bool) (L : Nat)
    (ha : a.length ≤ L) (hb : b.length ≤ L) :
    (bitFieldsEncode [a,b]).length ≤ bitPairSize L L := by
  have h := bitFieldsEncode_length_le [a,b] L (by
    intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl
    · exact ha
    · exact hb)
  norm_num only [List.length_cons,List.length_nil] at h
  change _ ≤ 5+2*(2*L.size+1+L) at h
  unfold bitPairSize
  omega
private theorem numeric_word_length (p n : Nat) (hn : n < p) :
    (uniformNatEncode n).length ≤ groupRecordBitBound p := by
  have hs := Nat.size_le_size (show n ≤ p-1 by omega)
  rw [uniformNatEncode_length]
  unfold groupRecordBitBound
  omega
private theorem numeric_pair_length (p a b : Nat) (ha : a < p) (hb : b < p) :
    (bitFieldsEncode [uniformNatEncode a,uniformNatEncode b]).length ≤ pairBound p :=
  pair_length_bound _ _ _ (numeric_word_length p a ha) (numeric_word_length p b hb)
private theorem numeric_statement_length (p g pk alpha beta : Nat)
    (hg : g < p) (hk : pk < p) (ha : alpha < p) (hb : beta < p) :
    (statement g pk alpha beta).length ≤ statementRecordBitBound p :=
  pair_length_bound _ _ _ (numeric_pair_length p g pk hg hk)
    (numeric_pair_length p alpha beta ha hb)
private theorem history_count_le (ws : List (List Bool)) :
    ws.length ≤ (bitFieldsEncode ws).length := by
  have h : ws.length ≤ (ws.map (fun w => 2*w.length.size+1+w.length)).sum := by
    induction ws with
    | nil => simp
    | cons w ws ih => simp only [List.length_cons,List.map_cons,List.sum_cons]; omega
  rw [bitFieldsEncode_length]
  omega

theorem clock_mono (p : Nat) {H N : Nat} (h : H ≤ N) : clock p H ≤ clock p N := by
  have hs := Nat.size_le_size h
  have ht := Nat.size_le_size (Nat.add_le_add_right h 1)
  unfold clock
  omega
end ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine
open Turing.TM2 BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
private theorem enter_start (old : Fin 48 → List Bool) (pair stmt hist : List Bool) :
    tick (state (some 0) 2 old pair stmt hist) = state (some (natLabel 0 0)) 2 old pair stmt hist := by rfl
private theorem pair_step (which : Bool) (old : Fin 48 → List Bool) (pair stmt hist : List Bool) :
    tick (state (some (if which then 3 else 1)) 2 old pair stmt hist) =
      state (some (writerLabel (if which then 1 else 0) 3)) 0 old
        (uniformNatEncode 2++pair) stmt hist := by
  cases which <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩ <;>
    congr 1 <;> funext k <;> fin_cases k <;> rfl
private theorem pair_zero (old : Fin 48 → List Bool) (pair stmt hist : List Bool) :
    tick (state (some 1) 2 old pair stmt hist) =
      state (some (writerLabel 0 3)) 0 old (uniformNatEncode 2++pair) stmt hist :=
  pair_step false old pair stmt hist
private theorem pair_one (old : Fin 48 → List Bool) (pair stmt hist : List Bool) :
    tick (state (some 3) 2 old pair stmt hist) =
      state (some (writerLabel 1 3)) 0 old (uniformNatEncode 2++pair) stmt hist :=
  pair_step true old pair stmt hist
private theorem next_pair (old : Fin 48 → List Bool) (pair stmt hist : List Bool) :
    tick (state (some 2) 2 old pair stmt hist) = state (some (natLabel 2 0)) 2 old pair stmt hist := by rfl
private theorem outer_step (old : Fin 48 → List Bool) (pair stmt hist : List Bool) :
    tick (state (some 4) 2 old pair stmt hist) =
      state (some (parseLabel 0)) 0 old pair (uniformNatEncode 2++stmt) hist := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl
private theorem parse_step (old : Fin 48 → List Bool) (pair stmt hist : List Bool) :
    tick (state (some 5) 2 old pair stmt hist) = state (some (incrementLabel 0)) 0 old pair stmt hist := by rfl
private theorem increment_step (old : Fin 48 → List Bool) (pair stmt hist : List Bool) :
    tick (state (some 6) 2 old pair stmt hist) = state (some (writerLabel 2 3)) 0 old pair stmt hist := by rfl
private theorem field_step (old : Fin 48 → List Bool) (pair stmt hist : List Bool) :
    tick (state (some 7) 2 old pair stmt hist) = state (some (writerLabel 3 5)) 0 old pair stmt hist := by rfl
private theorem halt_step (old : Fin 48 → List Bool) (hist : List Bool)
    (h28 : old 28 = []) (h29 : old 29 = []) :
    tick (state (some 8) 2 old [] [] hist) = result hist old := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> first | rfl | exact h28.symm | exact h29.symm
private theorem start_state (old : Fin 48 → List Bool) (hist : List Bool)
    (h28 : old 28 = []) (h29 : old 29 = []) (h47 : old 47 = hist) :
    start old = state (some 0) 2 old [] [] hist := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> first | rfl | exact h28 | exact h29 | exact h47

/-- Execute the nested statement codec and actual most-recent-first history update.
The source values and initial canonical history are local input specifications;
the enclosing source theorem derives them from its predecessor. -/
theorem run (p : Nat) (v : Fin 4 → Nat) (hs : List (List Bool)) (old : Fin 48 → List Bool)
    (hw : ∀ j : Fin 7, old ⟨23+j.val,by omega⟩ = [])
    (hv : ∀ i, v i < p) (hn : ∀ i, old (sourcePort i) = (v i).bits)
    (hh : old 47 = bitFieldsEncode hs) :
    ∃ used ≤ clock p (old 47).length,
      tick^[used] (start old) = result (bitFieldsEncode (statement (v 3) (v 2) (v 1) (v 0)::hs)) old := by
  have hw5 : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = [] := fun j => hw ⟨j.val,by omega⟩
  let hist := bitFieldsEncode hs
  let b1 := NatFieldWriterMachine.encoded (v 0) []
  let b2 := NatFieldWriterMachine.encoded (v 1) b1
  let cp := uniformNatEncode 2++b2
  let s1 := fieldWord cp []
  let b3 := NatFieldWriterMachine.encoded (v 2) []
  let b4 := NatFieldWriterMachine.encoded (v 3) b3
  let gp := uniformNatEncode 2++b4
  let s2 := fieldWord gp s1
  let st := uniformNatEncode 2++s2
  let body := bitFramesEncode hs
  obtain ⟨a,ha,ea⟩ := nat_run 0 (v 0) old [] [] hist hw5 (hn 0)
  obtain ⟨b,hb,eb⟩ := nat_run 1 (v 1) old b1 [] hist hw5 (hn 1)
  obtain ⟨c,hc,ec⟩ := field_run 0 old cp [] hist hw5
  obtain ⟨d,hd,ed⟩ := nat_run 2 (v 2) old [] s1 hist hw5 (hn 2)
  obtain ⟨e,he,ee⟩ := nat_run 3 (v 3) old b3 s1 hist hw5 (hn 3)
  obtain ⟨f,hf,ef⟩ := field_run 1 old gp s1 hist hw5
  obtain ⟨g,hg,eg⟩ := parse_history_run hs.length st body old hw5
  obtain ⟨h,hi,eh⟩ := increment_history_run hs.length st body old hw5
  obtain ⟨i,hj,ei⟩ := field_run 2 old (hs.length+1).bits st body hw5
  obtain ⟨j,hk,ej⟩ := prefix_history_run (hs.length+1) [] (fieldWord st body) old hw5
  change tick^[a] (state (some (natLabel 0 0)) 2 old [] [] hist) =
    state (some (natLabel 1 0)) 2 old b1 [] hist at ea
  change tick^[b] (state (some (natLabel 1 0)) 2 old b1 [] hist) = state (some 1) 2 old b2 [] hist at eb
  change tick^[c] (state (some (writerLabel 0 3)) 0 old cp [] hist) = state (some 2) 2 old [] s1 hist at ec
  change tick^[d] (state (some (natLabel 2 0)) 2 old [] s1 hist) = state (some (natLabel 3 0)) 2 old b3 s1 hist at ed
  change tick^[e] (state (some (natLabel 3 0)) 2 old b3 s1 hist) = state (some 3) 2 old b4 s1 hist at ee
  change tick^[f] (state (some (writerLabel 1 3)) 0 old gp s1 hist) = state (some 4) 2 old [] s2 hist at ef
  change tick^[g] (state (some (parseLabel 0)) 0 old [] st hist) = state (some 5) 2 old hs.length.bits st body at eg
  change tick^[i] (state (some (writerLabel 2 3)) 0 old (hs.length+1).bits st body) =
    state (some 7) 2 old (hs.length+1).bits [] (fieldWord st body) at ei
  let used := 1+(j+(1+(i+(1+(h+(1+(g+(1+(f+(1+(e+(d+(1+(c+(1+(b+(a+1)))))))))))))))))
  have execution : tick^[used] (start old) =
      result (uniformNatEncode (hs.length+1)++fieldWord st body) old := by
    rw [start_state old hist (hw 5) (hw 6) hh]
    dsimp only [used]
    rw [Function.iterate_add_apply tick 1,Function.iterate_add_apply tick j,
      Function.iterate_add_apply tick 1,Function.iterate_add_apply tick i,
      Function.iterate_add_apply tick 1,Function.iterate_add_apply tick h,
      Function.iterate_add_apply tick 1,Function.iterate_add_apply tick g,
      Function.iterate_add_apply tick 1,Function.iterate_add_apply tick f,
      Function.iterate_add_apply tick 1,Function.iterate_add_apply tick e,
      Function.iterate_add_apply tick d,Function.iterate_add_apply tick 1,
      Function.iterate_add_apply tick c,Function.iterate_add_apply tick 1,
      Function.iterate_add_apply tick b,Function.iterate_add_apply tick a,
      Function.iterate_one,enter_start,ea,eb,pair_zero,ec,next_pair,ed,ee,pair_one,ef,
      outer_step,eg,parse_step,eh,increment_step,ei,field_step,ej,halt_step old _ (hw 5) (hw 6)]
  have cp_eq : cp = bitFieldsEncode [uniformNatEncode (v 1),uniformNatEncode (v 0)] := by
    simp [cp,b2,b1,NatFieldWriterMachine.encoded,bitFieldsEncode,bitFramesEncode,List.append_assoc]
  have gp_eq : gp = bitFieldsEncode [uniformNatEncode (v 3),uniformNatEncode (v 2)] := by
    simp [gp,b4,b3,NatFieldWriterMachine.encoded,bitFieldsEncode,bitFramesEncode,List.append_assoc]
  have st_eq : st = statement (v 3) (v 2) (v 1) (v 0) := by
    change uniformNatEncode 2++fieldWord gp (fieldWord cp []) =
      bitFieldsEncode [bitFieldsEncode [uniformNatEncode (v 3),uniformNatEncode (v 2)],
        bitFieldsEncode [uniformNatEncode (v 1),uniformNatEncode (v 0)]]
    rw [←gp_eq,←cp_eq]
    simp only [bitFieldsEncode,bitFramesEncode,List.length_cons,List.length_nil,
      fieldWord,List.append_nil,List.append_assoc]
  have boundNat (k : Fin 4) : NatFieldWriterMachine.clock (v k) ≤ NatFieldWriterMachine.clock (p-1) :=
    NatFieldWriterMachine.clock_mono (by have := hv k; omega)
  have ba:=ha.trans (boundNat 0); have bb:=hb.trans (boundNat 1)
  have bd:=hd.trans (boundNat 2); have be:=he.trans (boundNat 3)
  have bc : c ≤ FrameWriteMachine.cost (pairBound p) := hc.trans (FrameWriteMachine.cost_mono (by
    rw [cp_eq]; exact numeric_pair_length p _ _ (hv 1) (hv 0)))
  have bf : f ≤ FrameWriteMachine.cost (pairBound p) := hf.trans (FrameWriteMachine.cost_mono (by
    rw [gp_eq]; exact numeric_pair_length p _ _ (hv 3) (hv 2)))
  have bi : i ≤ FrameWriteMachine.cost (statementRecordBitBound p) := hj.trans (FrameWriteMachine.cost_mono (by
    rw [st_eq]; exact numeric_statement_length p _ _ _ _ (hv 3) (hv 2) (hv 1) (hv 0)))
  have hlen : hs.length ≤ (old 47).length := by rw [hh]; exact history_count_le hs
  have hsiz:=Nat.size_le_size hlen
  have hnext:=Nat.size_le_size (Nat.add_le_add_right hlen 1)
  refine ⟨used,?_,?_⟩
  · dsimp only [used]
    unfold clock
    clear * - ba bb bc bd be bf bi hg hi hk hsiz hnext
    simp only [←Nat.add_assoc]
    omega
  · rw [st_eq] at execution
    simpa only [bitFieldsEncode,List.length_cons,bitFramesEncode,fieldWord,body,List.append_assoc] using execution


theorem padded_bounded (p N : Nat) (v : Fin 4 → Nat) (hs : List (List Bool)) (old : Fin 48 → List Bool)
    (hw : ∀ j : Fin 7, old ⟨23+j.val,by omega⟩ = [])
    (hv : ∀ i, v i < p) (hn : ∀ i, old (sourcePort i) = (v i).bits)
    (hh : old 47 = bitFieldsEncode hs) (hN : (old 47).length ≤ N) :
    tick^[clock p N] (start old) = result (bitFieldsEncode (statement (v 3) (v 2) (v 1) (v 0)::hs)) old := by
  obtain ⟨u,hu,he⟩ := run p v hs old hw hv hn hh
  have hb := hu.trans (clock_mono p hN)
  rw [show clock p N = (clock p N-u)+u by omega,Function.iterate_add_apply,he]
  exact Function.iterate_fixed (show tick (result _ old) = _ from rfl) _

theorem padded_run (p : Nat) (v : Fin 4 → Nat) (hs : List (List Bool)) (old : Fin 48 → List Bool)
    (hw : ∀ j : Fin 7, old ⟨23+j.val,by omega⟩ = [])
    (hv : ∀ i, v i < p) (hn : ∀ i, old (sourcePort i) = (v i).bits)
    (hh : old 47 = bitFieldsEncode hs) :
    tick^[clock p (old 47).length] (start old) = result (bitFieldsEncode (statement (v 3) (v 2) (v 1) (v 0)::hs)) old :=
  padded_bounded p _ v hs old hw hv hn hh (le_refl _)

theorem local_cost (l : Fin size) : BitOracleMachine.localCost (program l) ≤ 32 := by
  fin_cases l <;> decide +kernel

theorem charged_bounded (p N : Nat) (v : Fin 4 → Nat) (hs : List (List Bool)) (old : Fin 48 → List Bool)
    (hw : ∀ j : Fin 7, old ⟨23+j.val,by omega⟩ = [])
    (hv : ∀ i, v i < p) (hn : ∀ i, old (sourcePort i) = (v i).bits)
    (hh : old 47 = bitFieldsEncode hs) (hN : (old 47).length ≤ N) :
    ∃ charge ≤ cost p N, BitOracleMachine.run code (clock p N) (start old) =
      pure (result (bitFieldsEncode (statement (v 3) (v 2) (v 1) (v 0)::hs)) old,charge) := by
  obtain ⟨charge,hc,he⟩ := BitOracleMachine.compute_run_cost program 32 local_cost (clock p N) (start old)
  rw [show (TM2ReturnLink.tick program)^[clock p N] (start old) =
    result (bitFieldsEncode (statement (v 3) (v 2) (v 1) (v 0)::hs)) old
    from padded_bounded p N v hs old hw hv hn hh hN] at he
  exact ⟨charge,hc,he⟩

theorem charged (p : Nat) (v : Fin 4 → Nat) (hs : List (List Bool)) (old : Fin 48 → List Bool)
    (hw : ∀ j : Fin 7, old ⟨23+j.val,by omega⟩ = [])
    (hv : ∀ i, v i < p) (hn : ∀ i, old (sourcePort i) = (v i).bits)
    (hh : old 47 = bitFieldsEncode hs) :
    ∃ charge ≤ cost p (old 47).length,
      BitOracleMachine.run code (clock p (old 47).length) (start old) =
        pure (result (bitFieldsEncode (statement (v 3) (v 2) (v 1) (v 0)::hs)) old,charge) :=
  charged_bounded p _ v hs old hw hv hn hh (le_refl _)

#print axioms run
#print axioms padded_run
#print axioms padded_bounded
#print axioms local_cost
#print axioms charged
#print axioms charged_bounded
end ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine
