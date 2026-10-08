import ExplainableCrypto.Helios.Computational.ScalarComplementMachineRun
import ExplainableCrypto.Helios.Computational.ScalarDifferenceMachine
import ExplainableCrypto.Helios.Computational.BitPortTransfer

/-! Fixed executed handoff between honest proof requests. Original nonce/vote,
prior proofs/ciphertexts and current state remain in the surrounding 58 words. -/
namespace ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry
open Turing.TM2 BitOracleMachine
set_option maxRecDepth 65536
abbrev size := 119

def transferP1Layout : Fin 3 ⊕ Fin 55 ≃ Fin 58 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [21, 50, 23, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 51, 52, 53, 54, 55, 56, 57] (by decide +kernel) (by decide +kernel))

def complementLayout : Fin 8 ⊕ Fin 50 ≃ Fin 58 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [2, 21, 23, 24, 25, 26, 27, 28, 0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57] (by decide +kernel) (by decide +kernel))

def copyLayout : Fin 3 ⊕ Fin 55 ≃ Fin 58 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [20, 23, 24, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57] (by decide +kernel) (by decide +kernel))

def parseLayout : Fin 4 ⊕ Fin 54 ≃ Fin 58 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [23, 24, 25, 27, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 26, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57] (by decide +kernel) (by decide +kernel))

def addLayout : Fin 8 ⊕ Fin 50 ≃ Fin 58 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [27, 28, 23, 24, 25, 26, 2, 29, 0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57] (by decide +kernel) (by decide +kernel))

def writerLayout : Fin 5 ⊕ Fin 53 ≃ Fin 58 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [25, 23, 24, 50, 27, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 26, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 51, 52, 53, 54, 55, 56, 57] (by decide +kernel) (by decide +kernel))

def transferVoteLayout : Fin 3 ⊕ Fin 55 ≃ Fin 58 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [18, 51, 23, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 52, 53, 54, 55, 56, 57] (by decide +kernel) (by decide +kernel))

def transferLabels : BitPortTransfer.Label ≃ Fin 4 where
  toFun | .clear => 0 | .copy false => 1 | .copy true => 2 | .done => 3
  invFun k := if k = 0 then .clear else if k = 1 then .copy false else if k = 2 then .copy true else .done
  left_inv k := by cases k with
    | clear => rfl
    | copy b => cases b <;> rfl
    | done => rfl
  right_inv k := by fin_cases k <;> rfl

def transferProgram (total : Bool) (l : Fin 4) :=
  TM2StackFrame.relocate (if total then transferVoteLayout else transferP1Layout)
    (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.copyPorts transferLabels
      BinaryModuloCode.memory (BitPortTransfer.program false) l)
def complementProgram (l : Fin 21) := TM2StackFrame.relocate complementLayout (ScalarComplementMachine.program l)
def copyProgram (l : Fin 2) := TM2StackFrame.relocate copyLayout
  (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.copyPorts PrimeNonceCiphertextMachine.copyLabels
    BinaryModuloCode.memory BitCopyMachine.program l)
def parseProgram (l : Fin 3) := TM2StackFrame.relocate parseLayout
  (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.parsePorts PrimeNonceCiphertextMachine.parseLabels
    BinaryModuloCode.memory NatPrefixMachine.program l)
def addProgram (l : Fin 42) := TM2StackFrame.relocate addLayout (BinaryModAddMachine.program l)
def writerProgram (l : Fin 8) := TM2StackFrame.relocate writerLayout
  (TM2FiniteCoordinates.program ScalarDifferenceMachine.writerPorts CacheRoutineCode.writerLabels
    BinaryModuloCode.memory FrameWriteMachine.program l)

def stalePorts : Fin 15 → Fin 58 := ![1,3,7,10,11,12,13,38,39,40,42,43,49,50,51]
def finalPorts : Fin 8 → Fin 58 := ![2,23,24,25,26,27,28,29]
def transferLabel (total : Bool) (l : Fin 4) : Fin size :=
  ⟨(if total then 115 else 35)+l.val,by cases total <;> have := l.isLt <;> dsimp [size] <;> omega⟩
def complementLabel (l : Fin 21) : Fin size := ⟨39+l.val,by have := l.isLt; dsimp [size]; omega⟩
def copyLabel (l : Fin 2) : Fin size := ⟨60+l.val,by have := l.isLt; dsimp [size]; omega⟩
def parseLabel (l : Fin 3) : Fin size := ⟨62+l.val,by have := l.isLt; dsimp [size]; omega⟩
def addLabel (l : Fin 42) : Fin size := ⟨65+l.val,by have := l.isLt; dsimp [size]; omega⟩
def writerLabel (l : Fin 8) : Fin size := ⟨107+l.val,by have := l.isLt; dsimp [size]; omega⟩
def fail : Stmt (fun _ : Fin 58 => Bool) (Fin size) (Fin 3) := .load (fun _ => 1) .halt
def enter (l : Fin size) : Stmt (fun _ : Fin 58 => Bool) (Fin size) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => l))
def guard (l : Fin size) : Stmt (fun _ : Fin 58 => Bool) (Fin size) (Fin 3) :=
  .branch (fun v => v == 2) (enter l) fail

def program (l : Fin size) : Stmt (fun _ : Fin 58 => Bool) (Fin size) (Fin 3) :=
  if l = 0 then .branch (fun v => v == 2)
    (.push 37 (fun _ => false) (enter 12)) fail
  else if l = 1 then .branch (fun v => v == 2)
    (.push 37 (fun _ => true) (enter 12)) fail
  else if l = 2 then .pop 37 (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == 1) (enter (transferLabel false 0))
      (.branch (fun v => v == 2) (.load (fun _ => 2) (.goto (fun _ => complementLabel 0))) fail))
  else if l = 3 then .push 51 (fun _ => false) (enter 27)
  else if l = 4 then guard (copyLabel 0)
  else if l = 6 then .branch (fun v => v == 2)
    (.peek 23 (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 0) (enter 7) fail)) fail
  else if l = 7 then .pop 26 (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == 0) (enter (addLabel (BinaryModAddMachine.subLabel 0 0)))
      (.goto (fun _ => 7)))
  else if l = 8 then guard (writerLabel (CacheRoutineCode.writerLabels .digits))
  else if l = 9 then guard (transferLabel true 0)
  else if l = 10 then enter 27
  else if h : 12 ≤ l.val ∧ l.val < 27 then
    .pop (stalePorts ⟨l.val-12,by omega⟩) (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 0)
        (enter (if l = 26 then 2 else ⟨l.val+1,by dsimp [size]; omega⟩)) (.goto (fun _ => l)))
  else if h : 27 ≤ l.val ∧ l.val < 35 then
    .pop (finalPorts ⟨l.val-27,by omega⟩) (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 0)
        (if l = 34 then .load (fun _ => 2) .halt else enter ⟨l.val+1,by dsimp [size]; omega⟩)
        (.goto (fun _ => l)))
  else if h : 35 ≤ l.val ∧ l.val < 39 then TM2ReturnLink.redirect (transferLabel false) 3
    (transferProgram false ⟨l.val-35,by omega⟩)
  else if h : 39 ≤ l.val ∧ l.val < 60 then TM2ReturnLink.redirect complementLabel 4
    (complementProgram ⟨l.val-39,by omega⟩)
  else if h : 60 ≤ l.val ∧ l.val < 62 then TM2ReturnLink.redirect copyLabel (parseLabel 0)
    (copyProgram ⟨l.val-60,by omega⟩)
  else if h : 62 ≤ l.val ∧ l.val < 65 then TM2ReturnLink.redirect parseLabel 6
    (parseProgram ⟨l.val-62,by omega⟩)
  else if h : 65 ≤ l.val ∧ l.val < 107 then TM2ReturnLink.redirect addLabel 8
    (addProgram ⟨l.val-65,by omega⟩)
  else if h : 107 ≤ l.val ∧ l.val < 115 then TM2ReturnLink.redirect writerLabel 9
    (writerProgram ⟨l.val-107,by omega⟩)
  else if h : 115 ≤ l.val then TM2ReturnLink.redirect (transferLabel true) 10
    (transferProgram true ⟨l.val-115,by have := l.isLt; dsimp [size] at this; omega⟩)
  else fail

def code : Code 58 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 58 size 3
def tick : Config → Config := TM2ReturnLink.tick program
def start (total : Bool) (old : Fin 58 → List Bool) : Config :=
  ⟨some (if total then 1 else 0),2,old⟩
def resultWords (old : Fin 58 → List Bool) (nonce vote : List Bool) : Fin 58 → List Bool :=
  let w := fun k => if k ∈ ([1,2,3,7,10,11,12,13,23,24,25,26,27,28,29,37,38,39,40,42,43,49,50,51] : List (Fin 58)) then [] else old k
  Function.update (Function.update w 50 nonce) 51 vote
def result (old : Fin 58 → List Bool) (nonce vote : List Bool) : Config :=
  ⟨none,2,resultWords old nonce vote⟩

/-- Conservative cap covering each real component clock and every clear/return.
N bounds the initially resident words that this controller clears or copies. -/
def clock (q N : Nat) : Nat := 40*N+20*(q-1).size+8*q.size+100+
  ScalarComplementMachine.clock q+BinaryModAddMachine.clock q
def cost (q N : Nat) : Nat := 32*clock q N
end ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry

namespace ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

theorem complement_code (l : Fin 21) : program (complementLabel l) =
    TM2ReturnLink.redirect complementLabel 4 (complementProgram l) := by fin_cases l <;> rfl
theorem copy_code (l : Fin 2) : program (copyLabel l) =
    TM2ReturnLink.redirect copyLabel (parseLabel 0) (copyProgram l) := by fin_cases l <;> rfl
theorem parse_code (l : Fin 3) : program (parseLabel l) =
    TM2ReturnLink.redirect parseLabel 6 (parseProgram l) := by fin_cases l <;> rfl
theorem add_code (l : Fin 42) : program (addLabel l) =
    TM2ReturnLink.redirect addLabel 8 (addProgram l) := by fin_cases l <;> rfl
theorem writer_code (l : Fin 8) : program (writerLabel l) =
    TM2ReturnLink.redirect writerLabel 9 (writerProgram l) := by fin_cases l <;> rfl

theorem complement_slice (q r2 : Nat) (hr2 : r2 < q) (frame : Fin 50 → List Bool) :
    ∃ u ≤ ScalarComplementMachine.clock q,
      tick^[u] (TM2ReturnLink.embed complementLabel 4 (TM2StackFrame.embed complementLayout
        (ScalarComplementMachine.start q.bits (uniformNatEncode r2)) frame)) =
      TM2ReturnLink.embed complementLabel 4 (TM2StackFrame.embed complementLayout
        (ScalarComplementMachine.result q.bits (uniformNatEncode r2) r2.bits (q-r2).bits) frame) := by
  have hc := TM2StackFrame.run complementLayout ScalarComplementMachine.program
    (ScalarComplementMachine.clock q) (ScalarComplementMachine.start q.bits (uniformNatEncode r2)) frame
  change (TM2ReturnLink.tick complementProgram)^[ScalarComplementMachine.clock q] _ = _ at hc
  change _ = TM2StackFrame.embed complementLayout
    (ScalarComplementMachine.tick^[ScalarComplementMachine.clock q]
      (ScalarComplementMachine.start q.bits (uniformNatEncode r2))) frame at hc
  rw [ScalarComplementMachine.padded_run q r2 hr2] at hc
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run complementProgram program complementLabel 4 complement_code
    (ScalarComplementMachine.clock q) _ (by rw [hc]; rfl)
  rw [hc] at he
  exact ⟨u,hu,he⟩

theorem add_slice (q r1 r2 : Nat) (hr1 : r1 < q) (hr2 : r2 < q) (frame : Fin 50 → List Bool) :
    ∃ u ≤ BinaryModAddMachine.clock q,
      tick^[u] (TM2ReturnLink.embed addLabel 8 (TM2StackFrame.embed addLayout
        (BinaryModAddMachine.start r1.bits (q-r2).bits q.bits) frame)) =
      TM2ReturnLink.embed addLabel 8 (TM2StackFrame.embed addLayout
        (BinaryModAddMachine.result ((r1+r2)%q).bits (q-r2).bits q.bits) frame) := by
  have hc := TM2StackFrame.run addLayout BinaryModAddMachine.program
    (BinaryModAddMachine.clock q) (BinaryModAddMachine.start r1.bits (q-r2).bits q.bits) frame
  change (TM2ReturnLink.tick addProgram)^[BinaryModAddMachine.clock q] _ = _ at hc
  change _ = TM2StackFrame.embed addLayout
    (BinaryModAddMachine.tick^[BinaryModAddMachine.clock q]
      (BinaryModAddMachine.start r1.bits (q-r2).bits q.bits)) frame at hc
  rw [BinaryModAddMachine.run q r2 r1 hr2 hr1] at hc
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run addProgram program addLabel 8 add_code
    (BinaryModAddMachine.clock q) _ (by rw [hc]; rfl)
  rw [hc] at he
  exact ⟨u,hu,he⟩

def copyPresent (phase : Option Bool) (word target : List Bool) :=
  TM2FiniteCoordinates.present PrimeNonceCiphertextMachine.copyPorts
    PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory
    (BitCopyMachine.config phase word target [])
theorem copy_slice (word : List Bool) (frame : Fin 55 → List Bool) :
    ∃ u ≤ 2*word.length+2,
      tick^[u] (TM2ReturnLink.embed copyLabel (parseLabel 0) (TM2StackFrame.embed copyLayout
        (copyPresent (some false) word []) frame)) =
      TM2ReturnLink.embed copyLabel (parseLabel 0) (TM2StackFrame.embed copyLayout
        (copyPresent none word word) frame) := by
  have hi := TM2FiniteCoordinates.run PrimeNonceCiphertextMachine.copyPorts
    PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory BitCopyMachine.program
    (2*word.length+2) (BitCopyMachine.config (some false) word [] [])
  have hn := BitCopyMachine.run word [] none
  simp only [List.append_nil] at hn
  change (TM2ReturnLink.tick BitCopyMachine.program)^[2*word.length+2] _ = _ at hn
  rw [hn] at hi
  have hc := TM2StackFrame.run copyLayout
    (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.copyPorts
      PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory BitCopyMachine.program)
    (2*word.length+2) (copyPresent (some false) word []) frame
  dsimp only [copyPresent] at hc
  rw [hi] at hc
  change (TM2ReturnLink.tick copyProgram)^[2*word.length+2]
    (TM2StackFrame.embed copyLayout (copyPresent (some false) word []) frame) =
    TM2StackFrame.embed copyLayout (copyPresent none word word) frame at hc
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run copyProgram program copyLabel (parseLabel 0) copy_code
    (2*word.length+2) _ (by rw [hc]; rfl)
  rw [hc] at he
  exact ⟨u,hu,he⟩

def parsePresent (phase : Option NatPrefixMachine.Label) (word digits : List Bool) (v : Option Bool) :=
  TM2FiniteCoordinates.present PrimeNonceCiphertextMachine.parsePorts
    PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory
    (NatPrefixMachine.config phase word [] [] digits v)
theorem parse_slice (r : Nat) (frame : Fin 54 → List Bool) :
    ∃ u ≤ 3*r.size+3,
      tick^[u] (TM2ReturnLink.embed parseLabel 6 (TM2StackFrame.embed parseLayout
        (parsePresent (some .width) (uniformNatEncode r) [] none) frame)) =
      TM2ReturnLink.embed parseLabel 6 (TM2StackFrame.embed parseLayout
        (parsePresent none [] r.bits (some true)) frame) := by
  have hi := TM2FiniteCoordinates.run PrimeNonceCiphertextMachine.parsePorts
    PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory NatPrefixMachine.program
    (3*r.size+3) (NatPrefixMachine.config (some .width) (uniformNatEncode r) [] [] [] none)
  have hn := NatPrefixMachine.encoded_run r []
  simp only [List.append_nil] at hn
  change (TM2ReturnLink.tick NatPrefixMachine.program)^[3*r.size+3]
    (NatPrefixMachine.config (some .width) (uniformNatEncode r) [] [] [] none) = _ at hn
  rw [hn] at hi
  have hc := TM2StackFrame.run parseLayout
    (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.parsePorts
      PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory NatPrefixMachine.program)
    (3*r.size+3) (parsePresent (some .width) (uniformNatEncode r) [] none) frame
  dsimp only [parsePresent] at hc
  rw [hi] at hc
  change (TM2ReturnLink.tick parseProgram)^[3*r.size+3]
    (TM2StackFrame.embed parseLayout (parsePresent (some .width) (uniformNatEncode r) [] none) frame) =
    TM2StackFrame.embed parseLayout (parsePresent none [] r.bits (some true)) frame at hc
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run parseProgram program parseLabel 6 parse_code
    (3*r.size+3) _ (by rw [hc]; rfl)
  rw [hc] at he
  exact ⟨u,hu,he⟩

def writerPresent (phase : Option FrameWriteMachine.Label) (n word : List Bool) (v : Option Bool) :=
  TM2FiniteCoordinates.present ScalarDifferenceMachine.writerPorts CacheRoutineCode.writerLabels
    BinaryModuloCode.memory (FrameWriteMachine.state phase [] [] [] word n v)
theorem writer_slice (r : Nat) (frame : Fin 53 → List Bool) :
    ∃ u ≤ 3*r.size+3,
      tick^[u] (TM2ReturnLink.embed writerLabel 9 (TM2StackFrame.embed writerLayout
        (writerPresent (some .digits) r.bits [] none) frame)) =
      TM2ReturnLink.embed writerLabel 9 (TM2StackFrame.embed writerLayout
        (writerPresent none [] (uniformNatEncode r) (some true)) frame) := by
  have hi := TM2FiniteCoordinates.run ScalarDifferenceMachine.writerPorts CacheRoutineCode.writerLabels
    BinaryModuloCode.memory FrameWriteMachine.program (3*r.size+3)
    (FrameWriteMachine.state (some .digits) [] [] [] [] r.bits none)
  have hn := FrameWriteMachine.prefix_run r [] none
  simp only [List.append_nil] at hn
  change (TM2ReturnLink.tick FrameWriteMachine.program)^[3*r.size+3] _ = _ at hn
  rw [hn] at hi
  have hc := TM2StackFrame.run writerLayout
    (TM2FiniteCoordinates.program ScalarDifferenceMachine.writerPorts CacheRoutineCode.writerLabels
      BinaryModuloCode.memory FrameWriteMachine.program)
    (3*r.size+3) (writerPresent (some .digits) r.bits [] none) frame
  dsimp only [writerPresent] at hc
  rw [hi] at hc
  change (TM2ReturnLink.tick writerProgram)^[3*r.size+3]
    (TM2StackFrame.embed writerLayout (writerPresent (some .digits) r.bits [] none) frame) =
    TM2StackFrame.embed writerLayout (writerPresent none [] (uniformNatEncode r) (some true)) frame at hc
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run writerProgram program writerLabel 9 writer_code
    (3*r.size+3) _ (by rw [hc]; rfl)
  rw [hc] at he
  exact ⟨u,hu,he⟩
#print axioms complement_slice
#print axioms add_slice
#print axioms copy_slice
#print axioms parse_slice
#print axioms writer_slice
end ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry

namespace ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry
open Turing.TM2 BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

private theorem transfer_code (total : Bool) (l : Fin 4) :
    program (transferLabel total l) = TM2ReturnLink.redirect (transferLabel total)
      (if total then 10 else 3) (transferProgram total l) := by
  cases total <;> fin_cases l <;> rfl

private def transferFrame (total : Bool) (W : Fin 58 → List Bool) : Fin 55 → List Bool :=
  fun j => W ((if total then transferVoteLayout else transferP1Layout) (.inr j))
private def transferState (total : Bool) (phase : Option BitPortTransfer.Label)
    (word old : List Bool) (frame : Fin 55 → List Bool) : BitOracleMachine.Config 58 4 3 :=
  TM2StackFrame.embed (if total then transferVoteLayout else transferP1Layout)
    (TM2FiniteCoordinates.present PrimeNonceCiphertextMachine.copyPorts transferLabels
      BinaryModuloCode.memory (BitPortTransfer.config phase word old [])) frame

private theorem transfer_initial (total : Bool) (W : Fin 58 → List Bool) (hs : W 23 = []) :
    transferState total (some .clear) (W (if total then 18 else 21)) (W (if total then 51 else 50))
      (transferFrame total W) = (⟨some 0,0,W⟩ : BitOracleMachine.Config 58 4 3) := by
  have hwords (k : Fin 58) :
      (transferState total (some .clear) (W (if total then 18 else 21)) (W (if total then 51 else 50))
        (transferFrame total W)).stk k = W k := by
    obtain ⟨x,rfl⟩ := (if total then transferVoteLayout else transferP1Layout).surjective k
    cases x with
    | inl i =>
      simp only [transferState,TM2StackFrame.embed,TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl]
      cases total <;> fin_cases i <;> first | rfl | exact hs.symm
    | inr j =>
      simp only [transferState,TM2StackFrame.embed,TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inr]
      rfl
  exact congrArg (fun w => (⟨some 0,0,w⟩ : BitOracleMachine.Config 58 4 3)) (funext hwords)

private theorem transfer_final (total : Bool) (W : Fin 58 → List Bool) (hs : W 23 = []) :
    transferState total none (W (if total then 18 else 21)) (W (if total then 18 else 21))
      (transferFrame total W) =
    (⟨none,0,Function.update W (if total then 51 else 50) (W (if total then 18 else 21))⟩ :
      BitOracleMachine.Config 58 4 3) := by
  have hwords (k : Fin 58) :
      (transferState total none (W (if total then 18 else 21)) (W (if total then 18 else 21))
        (transferFrame total W)).stk k =
      Function.update W (if total then 51 else 50) (W (if total then 18 else 21)) k := by
    obtain ⟨x,rfl⟩ := (if total then transferVoteLayout else transferP1Layout).surjective k
    cases x with
    | inl i =>
      simp only [transferState,TM2StackFrame.embed,TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl]
      cases total <;> fin_cases i <;> first | rfl | exact hs.symm
    | inr j =>
      simp only [transferState,TM2StackFrame.embed,TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inr]
      cases total <;> fin_cases j <;> rfl
  exact congrArg (fun w => (⟨none,0,w⟩ : BitOracleMachine.Config 58 4 3)) (funext hwords)

/-- Both actual source-preserving replacements, including old destination cleanup,
return to their real live labels and preserve every other caller word. -/
theorem transfer_run (total : Bool) (W : Fin 58 → List Bool) (hs : W 23 = []) :
    ∃ used ≤ (W (if total then 51 else 50)).length + 2*(W (if total then 18 else 21)).length+4,
      tick^[used] (⟨some (transferLabel total 0),0,W⟩ : Config) =
      ⟨some (if total then 10 else 3),0,
        Function.update W (if total then 51 else 50) (W (if total then 18 else 21))⟩ := by
  obtain ⟨u,hu,he⟩ := BitPortTransfer.run (W (if total then 18 else 21))
    (W (if total then 51 else 50)) none
  have hc : (TM2ReturnLink.tick (transferProgram total))^[u]
      (transferState total (some .clear) (W (if total then 18 else 21)) (W (if total then 51 else 50))
        (transferFrame total W)) =
      transferState total none (W (if total then 18 else 21)) (W (if total then 18 else 21))
        (transferFrame total W) := by
    unfold transferProgram transferState
    rw [TM2StackFrame.run,TM2FiniteCoordinates.run,he]
  obtain ⟨used,hused,hex⟩ := TM2ReturnLink.run (transferProgram total) program (transferLabel total)
    (if total then 10 else 3) (transfer_code total) u _ (by rw [hc]; rfl)
  rw [hc,transfer_initial total W hs,transfer_final total W hs] at hex
  exact ⟨used,hused.trans hu,hex⟩

#print axioms transfer_run
end ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry

namespace ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

def clearPort (j : Fin 23) : Fin 58 :=
  if h : j.val < 15 then stalePorts ⟨j.val,h⟩ else finalPorts ⟨j.val-15,by omega⟩
def clearLabel (j : Fin 23) : Fin size := ⟨12+j.val,by have := j.isLt; dsimp [size]; omega⟩
def clearNext (j : Fin 23) : Option (Fin size) :=
  if j = 22 then none else some (if j = 14 then 2 else ⟨13+j.val,by have := j.isLt; dsimp [size]; omega⟩)
def clearMemory (j : Fin 23) : Fin 3 := if j = 22 then 2 else 0

theorem clear_instruction (j : Fin 23) : program (clearLabel j) =
    .pop (clearPort j) (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 0)
        (.load (fun _ => clearMemory j) (match clearNext j with
          | none => .halt | some next => .goto (fun _ => next)))
        (.goto (fun _ => clearLabel j))) := by
  fin_cases j <;> rfl

private def clearing (j : Fin 23) (W : Fin 58 → List Bool) (word : List Bool) (v : Fin 3) : Config :=
  ⟨some (clearLabel j),v,Function.update W (clearPort j) word⟩
private def cleared (j : Fin 23) (W : Fin 58 → List Bool) : Config :=
  ⟨clearNext j,clearMemory j,Function.update W (clearPort j) []⟩

theorem clear_word (j : Fin 23) (W : Fin 58 → List Bool) (word : List Bool) (v : Fin 3) :
    tick^[word.length+1] (clearing j W word v) = cleared j W := by
  induction word generalizing v with
  | nil =>
    simp only [List.length_nil,Nat.zero_add,Function.iterate_one]
    simp [tick,TM2ReturnLink.tick,clearing,cleared,clear_instruction,step,stepAux]
    cases clearNext j <;> simp [BinaryModuloCode.memory]
  | cons b word ih =>
    have hs : tick (clearing j W (b::word) v) = clearing j W word (BinaryModuloCode.memory (some b)) := by
      simp [tick,TM2ReturnLink.tick,clearing,clear_instruction,step,stepAux]
      cases b <;> rfl
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,hs]
    exact ih _

#print axioms clear_word
end ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry

namespace ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

def staleCleared (old : Fin 58 → List Bool) (k : Fin 58) : List Bool :=
  if k ∈ ([1,3,7,10,11,12,13,38,39,40,42,43,49,50,51] : List (Fin 58)) then [] else old k

def finalCleared (old : Fin 58 → List Bool) (k : Fin 58) : List Bool :=
  if k ∈ ([2,23,24,25,26,27,28,29] : List (Fin 58)) then [] else old k

private theorem clear_existing (j : Fin 23) (old : Fin 58 → List Bool) (v : Fin 3) :
    tick^[(old (clearPort j)).length+1] (⟨some (clearLabel j),v,old⟩ : Config) =
      ⟨clearNext j,clearMemory j,Function.update old (clearPort j) []⟩ := by
  simpa only [clearing,cleared,Function.update_eq_self] using clear_word j old (old (clearPort j)) v

private theorem clear_segment_chain {a b : Nat} {x y z : Config}
    (ha : tick^[a] x = y) (hb : tick^[b] y = z) : tick^[a+b] x = z := by
  rw [Nat.add_comm a b,Function.iterate_add_apply,ha,hb]

/-- Exact execution of the fixed 15-port cleanup segment, retaining the entire other frame. -/
theorem stale_clear_run (old : Fin 58 → List Bool) :
    tick^[(∑ j : Fin 15, ((old (stalePorts j)).length+1))]
      (⟨some 12,0,old⟩ : Config) = ⟨some 2,0,staleCleared old⟩ := by
  let w0 := old
  let w1 := Function.update w0 (1 : Fin 58) []
  let w2 := Function.update w1 (3 : Fin 58) []
  let w3 := Function.update w2 (7 : Fin 58) []
  let w4 := Function.update w3 (10 : Fin 58) []
  let w5 := Function.update w4 (11 : Fin 58) []
  let w6 := Function.update w5 (12 : Fin 58) []
  let w7 := Function.update w6 (13 : Fin 58) []
  let w8 := Function.update w7 (38 : Fin 58) []
  let w9 := Function.update w8 (39 : Fin 58) []
  let w10 := Function.update w9 (40 : Fin 58) []
  let w11 := Function.update w10 (42 : Fin 58) []
  let w12 := Function.update w11 (43 : Fin 58) []
  let w13 := Function.update w12 (49 : Fin 58) []
  let w14 := Function.update w13 (50 : Fin 58) []
  let w15 := Function.update w14 (51 : Fin 58) []
  have h0 : tick^[(old 1).length+1] (⟨some 12,0,w0⟩ : Config) =
      ⟨some 13,0,w1⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,Function.update] using clear_existing 0 w0 0
  have h1 : tick^[(old 3).length+1] (⟨some 13,0,w1⟩ : Config) =
      ⟨some 14,0,w2⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,Function.update] using clear_existing 1 w1 0
  have h2 : tick^[(old 7).length+1] (⟨some 14,0,w2⟩ : Config) =
      ⟨some 15,0,w3⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,Function.update] using clear_existing 2 w2 0
  have h3 : tick^[(old 10).length+1] (⟨some 15,0,w3⟩ : Config) =
      ⟨some 16,0,w4⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,w4,Function.update] using clear_existing 3 w3 0
  have h4 : tick^[(old 11).length+1] (⟨some 16,0,w4⟩ : Config) =
      ⟨some 17,0,w5⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,w4,w5,Function.update] using clear_existing 4 w4 0
  have h5 : tick^[(old 12).length+1] (⟨some 17,0,w5⟩ : Config) =
      ⟨some 18,0,w6⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,w4,w5,w6,Function.update] using clear_existing 5 w5 0
  have h6 : tick^[(old 13).length+1] (⟨some 18,0,w6⟩ : Config) =
      ⟨some 19,0,w7⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,w4,w5,w6,w7,Function.update] using clear_existing 6 w6 0
  have h7 : tick^[(old 38).length+1] (⟨some 19,0,w7⟩ : Config) =
      ⟨some 20,0,w8⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,w4,w5,w6,w7,w8,Function.update] using clear_existing 7 w7 0
  have h8 : tick^[(old 39).length+1] (⟨some 20,0,w8⟩ : Config) =
      ⟨some 21,0,w9⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,Function.update] using clear_existing 8 w8 0
  have h9 : tick^[(old 40).length+1] (⟨some 21,0,w9⟩ : Config) =
      ⟨some 22,0,w10⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,Function.update] using clear_existing 9 w9 0
  have h10 : tick^[(old 42).length+1] (⟨some 22,0,w10⟩ : Config) =
      ⟨some 23,0,w11⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,Function.update] using clear_existing 10 w10 0
  have h11 : tick^[(old 43).length+1] (⟨some 23,0,w11⟩ : Config) =
      ⟨some 24,0,w12⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,Function.update] using clear_existing 11 w11 0
  have h12 : tick^[(old 49).length+1] (⟨some 24,0,w12⟩ : Config) =
      ⟨some 25,0,w13⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,Function.update] using clear_existing 12 w12 0
  have h13 : tick^[(old 50).length+1] (⟨some 25,0,w13⟩ : Config) =
      ⟨some 26,0,w14⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,Function.update] using clear_existing 13 w13 0
  have h14 : tick^[(old 51).length+1] (⟨some 26,0,w14⟩ : Config) =
      ⟨some 2,0,w15⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,Function.update] using clear_existing 14 w14 0
  have h := h0
  have h := clear_segment_chain h h1
  have h := clear_segment_chain h h2
  have h := clear_segment_chain h h3
  have h := clear_segment_chain h h4
  have h := clear_segment_chain h h5
  have h := clear_segment_chain h h6
  have h := clear_segment_chain h h7
  have h := clear_segment_chain h h8
  have h := clear_segment_chain h h9
  have h := clear_segment_chain h h10
  have h := clear_segment_chain h h11
  have h := clear_segment_chain h h12
  have h := clear_segment_chain h h13
  have h := clear_segment_chain h h14
  have he : w15 = staleCleared old := by
    funext k
    fin_cases k <;> rfl
  rw [he] at h
  have ht : (∑ j : Fin 15, ((old (stalePorts j)).length+1)) = ((old 1).length+1)+((old 3).length+1)+((old 7).length+1)+((old 10).length+1)+((old 11).length+1)+((old 12).length+1)+((old 13).length+1)+((old 38).length+1)+((old 39).length+1)+((old 40).length+1)+((old 42).length+1)+((old 43).length+1)+((old 49).length+1)+((old 50).length+1)+((old 51).length+1) := by
    simp [Fin.sum_univ_succ,stalePorts,Nat.add_assoc]
  rw [ht]
  exact h

#print axioms stale_clear_run

/-- Exact execution of the fixed 8-port cleanup segment, retaining the entire other frame. -/
theorem final_clear_run (old : Fin 58 → List Bool) :
    tick^[(∑ j : Fin 8, ((old (finalPorts j)).length+1))]
      (⟨some 27,0,old⟩ : Config) = ⟨none,2,finalCleared old⟩ := by
  let w0 := old
  let w1 := Function.update w0 (2 : Fin 58) []
  let w2 := Function.update w1 (23 : Fin 58) []
  let w3 := Function.update w2 (24 : Fin 58) []
  let w4 := Function.update w3 (25 : Fin 58) []
  let w5 := Function.update w4 (26 : Fin 58) []
  let w6 := Function.update w5 (27 : Fin 58) []
  let w7 := Function.update w6 (28 : Fin 58) []
  let w8 := Function.update w7 (29 : Fin 58) []
  have h0 : tick^[(old 2).length+1] (⟨some 27,0,w0⟩ : Config) =
      ⟨some 28,0,w1⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,Function.update] using clear_existing 15 w0 0
  have h1 : tick^[(old 23).length+1] (⟨some 28,0,w1⟩ : Config) =
      ⟨some 29,0,w2⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,Function.update] using clear_existing 16 w1 0
  have h2 : tick^[(old 24).length+1] (⟨some 29,0,w2⟩ : Config) =
      ⟨some 30,0,w3⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,Function.update] using clear_existing 17 w2 0
  have h3 : tick^[(old 25).length+1] (⟨some 30,0,w3⟩ : Config) =
      ⟨some 31,0,w4⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,w4,Function.update] using clear_existing 18 w3 0
  have h4 : tick^[(old 26).length+1] (⟨some 31,0,w4⟩ : Config) =
      ⟨some 32,0,w5⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,w4,w5,Function.update] using clear_existing 19 w4 0
  have h5 : tick^[(old 27).length+1] (⟨some 32,0,w5⟩ : Config) =
      ⟨some 33,0,w6⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,w4,w5,w6,Function.update] using clear_existing 20 w5 0
  have h6 : tick^[(old 28).length+1] (⟨some 33,0,w6⟩ : Config) =
      ⟨some 34,0,w7⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,w4,w5,w6,w7,Function.update] using clear_existing 21 w6 0
  have h7 : tick^[(old 29).length+1] (⟨some 34,0,w7⟩ : Config) =
      ⟨none,2,w8⟩ := by
    simpa [size,Fin.ext_iff,clearPort,clearLabel,clearNext,clearMemory,stalePorts,finalPorts,
      w0,w1,w2,w3,w4,w5,w6,w7,w8,Function.update] using clear_existing 22 w7 0
  have h := h0
  have h := clear_segment_chain h h1
  have h := clear_segment_chain h h2
  have h := clear_segment_chain h h3
  have h := clear_segment_chain h h4
  have h := clear_segment_chain h h5
  have h := clear_segment_chain h h6
  have h := clear_segment_chain h h7
  have he : w8 = finalCleared old := by
    funext k
    fin_cases k <;> rfl
  rw [he] at h
  have ht : (∑ j : Fin 8, ((old (finalPorts j)).length+1)) = ((old 2).length+1)+((old 23).length+1)+((old 24).length+1)+((old 25).length+1)+((old 26).length+1)+((old 27).length+1)+((old 28).length+1)+((old 29).length+1) := by
    simp [Fin.sum_univ_succ,finalPorts,Nat.add_assoc]
  rw [ht]
  exact h

#print axioms final_clear_run
end ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry

namespace ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

def work (W : Fin 58 → List Bool) (x0 x1 x2 x3 x4 x5 x6 : List Bool) : Fin 58 → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update W 23 x0) 24 x1) 25 x2) 26 x3) 27 x4) 28 x5) 29 x6

def complementAfter (W : Fin 58 → List Bool) (q r2 : Nat) : Fin 58 → List Bool :=
  work W [] [] [] r2.bits [] (q-r2).bits []

theorem complement_phase (q r2 : Nat) (hr2 : r2 < q) (W : Fin 58 → List Bool)
    (hq : W 2 = q.bits) (hr : W 21 = uniformNatEncode r2)
    (hw : ∀ j : Fin 7, W ⟨23+j.val,by omega⟩ = []) :
    ∃ u ≤ ScalarComplementMachine.clock q,
      tick^[u] (⟨some (complementLabel 0),2,W⟩ : Config) =
        ⟨some 4,2,complementAfter W q r2⟩ := by
  let frame : Fin 50 → List Bool := fun j => W (complementLayout (.inr j))
  obtain ⟨u,hu,he⟩ := complement_slice q r2 hr2 frame
  have hw0 := hw 0; have hw1 := hw 1; have hw2 := hw 2; have hw3 := hw 3
  have hw4 := hw 4; have hw5 := hw 5; have hw6 := hw 6
  have hi : TM2StackFrame.data complementLayout
      (ScalarComplementMachine.start q.bits (uniformNatEncode r2)).stk frame = W := by
    funext k
    obtain ⟨x,rfl⟩ := complementLayout.surjective k
    cases x with
    | inl i =>
      simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> first | exact hq.symm | exact hr.symm | exact hw0.symm | exact hw1.symm | exact hw2.symm | exact hw3.symm | exact hw4.symm | exact hw5.symm
    | inr j => simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inr]; rfl
  have ho : TM2StackFrame.data complementLayout
      (ScalarComplementMachine.result q.bits (uniformNatEncode r2) r2.bits (q-r2).bits).stk frame =
      complementAfter W q r2 := by
    funext k
    obtain ⟨x,rfl⟩ := complementLayout.surjective k
    cases x with
    | inl i =>
      simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> first | rfl | exact hq.symm | exact hr.symm
    | inr j =>
      simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> first | rfl | exact hw6
  change tick^[u] (⟨some (complementLabel 0),2,_⟩ : Config) = ⟨some 4,2,_⟩ at he
  dsimp only [TM2StackFrame.embed] at he
  rw [hi,ho] at he
  exact ⟨u,hu,he⟩


theorem copy_phase (word : List Bool)  (W : Fin 58 → List Bool) (h20 : W 20 = word) (h23 : W 23 = []) (h24 : W 24 = []) :
    ∃ u ≤ 2*word.length+2,
      tick^[u] (⟨some (copyLabel 0),0,W⟩ : Config) =
        ⟨some (parseLabel 0),0,Function.update W 23 word⟩ := by
  let frame : Fin 55 → List Bool := fun j => W (copyLayout (.inr j))
  obtain ⟨u,hu,he⟩ := copy_slice word frame
  have hi : TM2StackFrame.data copyLayout (copyPresent (some false) word []).stk frame = W := by
    funext k
    obtain ⟨x,rfl⟩ := copyLayout.surjective k
    cases x with
    | inl i =>
      simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> first | rfl | exact h20.symm | exact h23.symm | exact h24.symm
    | inr j => simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inr]; rfl
  have ho : TM2StackFrame.data copyLayout (copyPresent none word word).stk frame = Function.update W 23 word := by
    funext k
    obtain ⟨x,rfl⟩ := copyLayout.surjective k
    cases x with
    | inl i =>
      simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> first | rfl | exact h20.symm | exact h23.symm | exact h24.symm
    | inr j =>
      simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  change tick^[u] (⟨some (copyLabel 0),0,_⟩ : Config) = ⟨some (parseLabel 0),0,_⟩ at he
  dsimp only [TM2StackFrame.embed] at he
  rw [hi,ho] at he
  exact ⟨u,hu,he⟩

theorem parse_phase (r : Nat)  (W : Fin 58 → List Bool) (h23 : W 23 = uniformNatEncode r) (h24 : W 24 = []) (h25 : W 25 = []) (h27 : W 27 = []) :
    ∃ u ≤ 3*r.size+3,
      tick^[u] (⟨some (parseLabel 0),0,W⟩ : Config) =
        ⟨some (6),2,Function.update (Function.update W 23 []) 27 r.bits⟩ := by
  let frame : Fin 54 → List Bool := fun j => W (parseLayout (.inr j))
  obtain ⟨u,hu,he⟩ := parse_slice r frame
  have hi : TM2StackFrame.data parseLayout (parsePresent (some .width) (uniformNatEncode r) [] none).stk frame = W := by
    funext k
    obtain ⟨x,rfl⟩ := parseLayout.surjective k
    cases x with
    | inl i =>
      simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> first | rfl | exact h23.symm | exact h24.symm | exact h25.symm | exact h27.symm
    | inr j => simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inr]; rfl
  have ho : TM2StackFrame.data parseLayout (parsePresent none [] r.bits (some true)).stk frame = Function.update (Function.update W 23 []) 27 r.bits := by
    funext k
    obtain ⟨x,rfl⟩ := parseLayout.surjective k
    cases x with
    | inl i =>
      simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> first | rfl | exact h23.symm | exact h24.symm | exact h25.symm
    | inr j =>
      simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  change tick^[u] (⟨some (parseLabel 0),0,_⟩ : Config) = ⟨some (6),2,_⟩ at he
  dsimp only [TM2StackFrame.embed] at he
  rw [hi,ho] at he
  exact ⟨u,hu,he⟩

theorem add_phase (q r1 r2 : Nat) (hr1 : r1 < q) (hr2 : r2 < q) (W : Fin 58 → List Bool) (h27 : W 27 = r1.bits) (h28 : W 28 = (q-r2).bits) (h2 : W 2 = q.bits) (h23 : W 23 = []) (h24 : W 24 = []) (h25 : W 25 = []) (h26 : W 26 = []) (h29 : W 29 = []) :
    ∃ u ≤ BinaryModAddMachine.clock q,
      tick^[u] (⟨some (addLabel (BinaryModAddMachine.subLabel 0 0)),0,W⟩ : Config) =
        ⟨some (8),2,Function.update W 27 ((r1+r2)%q).bits⟩ := by
  let frame : Fin 50 → List Bool := fun j => W (addLayout (.inr j))
  obtain ⟨u,hu,he⟩ := add_slice q r1 r2 hr1 hr2 frame
  have hi : TM2StackFrame.data addLayout (BinaryModAddMachine.start r1.bits (q-r2).bits q.bits).stk frame = W := by
    funext k
    obtain ⟨x,rfl⟩ := addLayout.surjective k
    cases x with
    | inl i =>
      simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> first | rfl | exact h27.symm | exact h28.symm | exact h2.symm | exact h23.symm | exact h24.symm | exact h25.symm | exact h26.symm | exact h29.symm
    | inr j => simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inr]; rfl
  have ho : TM2StackFrame.data addLayout (BinaryModAddMachine.result ((r1+r2)%q).bits (q-r2).bits q.bits).stk frame = Function.update W 27 ((r1+r2)%q).bits := by
    funext k
    obtain ⟨x,rfl⟩ := addLayout.surjective k
    cases x with
    | inl i =>
      simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> first | rfl | exact h27.symm | exact h28.symm | exact h2.symm | exact h23.symm | exact h24.symm | exact h25.symm | exact h26.symm | exact h29.symm
    | inr j =>
      simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  change tick^[u] (⟨some (addLabel (BinaryModAddMachine.subLabel 0 0)),0,_⟩ : Config) = ⟨some (8),2,_⟩ at he
  dsimp only [TM2StackFrame.embed] at he
  rw [hi,ho] at he
  exact ⟨u,hu,he⟩

theorem writer_phase (r : Nat)  (W : Fin 58 → List Bool) (h27 : W 27 = r.bits) (h23 : W 23 = []) (h24 : W 24 = []) (h25 : W 25 = []) (h50 : W 50 = []) :
    ∃ u ≤ 3*r.size+3,
      tick^[u] (⟨some (writerLabel (CacheRoutineCode.writerLabels .digits)),0,W⟩ : Config) =
        ⟨some (9),2,Function.update (Function.update W 27 []) 50 (uniformNatEncode r)⟩ := by
  let frame : Fin 53 → List Bool := fun j => W (writerLayout (.inr j))
  obtain ⟨u,hu,he⟩ := writer_slice r frame
  have hi : TM2StackFrame.data writerLayout (writerPresent (some .digits) r.bits [] none).stk frame = W := by
    funext k
    obtain ⟨x,rfl⟩ := writerLayout.surjective k
    cases x with
    | inl i =>
      simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> first | rfl | exact h27.symm | exact h23.symm | exact h24.symm | exact h25.symm | exact h50.symm
    | inr j => simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inr]; rfl
  have ho : TM2StackFrame.data writerLayout (writerPresent none [] (uniformNatEncode r) (some true)).stk frame = Function.update (Function.update W 27 []) 50 (uniformNatEncode r) := by
    funext k
    obtain ⟨x,rfl⟩ := writerLayout.surjective k
    cases x with
    | inl i =>
      simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> first | rfl | exact h27.symm | exact h23.symm | exact h24.symm | exact h25.symm
    | inr j =>
      simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  change tick^[u] (⟨some (writerLabel (CacheRoutineCode.writerLabels .digits)),0,_⟩ : Config) = ⟨some (9),2,_⟩ at he
  dsimp only [TM2StackFrame.embed] at he
  rw [hi,ho] at he
  exact ⟨u,hu,he⟩

#print axioms complement_phase
#print axioms copy_phase
#print axioms parse_phase
#print axioms add_phase
#print axioms writer_phase
end ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry

namespace ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry
open Turing.TM2 OracleComp OracleSpec
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
attribute [local irreducible] BitOracleMachine.run

def base (W : Fin 58 → List Bool) : Fin 58 → List Bool := Function.update (staleCleared W) 37 []
private theorem sequence {a b c : Config} {n m : Nat} (h : tick^[n] a = b) (g : tick^[m] b = c) :
    tick^[n+m] a = c := by rw [Nat.add_comm n m,Function.iterate_add_apply,h,g]

private theorem initial_step (total : Bool) (W : Fin 58 → List Bool) (hw : W 37 = []) :
    tick (start total W) = ⟨some 12,0,Function.update W 37 [total]⟩ := by
  cases total <;> simp [start,tick,TM2ReturnLink.tick,program,step,stepAux,enter,hw]

private theorem clear_marker (total : Bool) (W : Fin 58 → List Bool) :
    staleCleared (Function.update W 37 [total]) = Function.update (staleCleared W) 37 [total] := by
  funext k
  fin_cases k <;> rfl

private theorem dispatch_step (total : Bool) (W : Fin 58 → List Bool) :
    tick (⟨some 2,0,Function.update (staleCleared W) 37 [total]⟩ : Config) =
    (if total then ⟨some (complementLabel 0),2,base W⟩
      else ⟨some (transferLabel false 0),0,base W⟩) := by
  cases total <;> simp [tick,TM2ReturnLink.tick,program,step,stepAux,base,enter,BinaryModuloCode.memory]

private theorem setup_run (total : Bool) (W : Fin 58 → List Bool) (hw : W 37 = []) :
    tick^[1+(∑ j : Fin 15, ((W (stalePorts j)).length+1))+1] (start total W) =
    (if total then ⟨some (complementLabel 0),2,base W⟩
      else ⟨some (transferLabel false 0),0,base W⟩) := by
  have h0 : tick^[1] (start total W) = ⟨some 12,0,Function.update W 37 [total]⟩ := initial_step total W hw
  have h1 := stale_clear_run (Function.update W 37 [total])
  have hlength : (∑ j : Fin 15, (((Function.update W 37 [total]) (stalePorts j)).length+1)) =
      ∑ j : Fin 15, ((W (stalePorts j)).length+1) := by
    apply Finset.sum_congr rfl
    intro j hj
    fin_cases j <;> rfl
  rw [hlength,clear_marker] at h1
  have h2 : tick^[1] (⟨some 2,0,Function.update (staleCleared W) 37 [total]⟩ : Config) = _ :=
    dispatch_step total W
  exact sequence (sequence h0 h1) h2

private theorem clear26_run (W : Fin 58 → List Bool) :
    tick^[(W 26).length+1] (⟨some 7,0,W⟩ : Config) =
      ⟨some (addLabel (BinaryModAddMachine.subLabel 0 0)),0,Function.update W 26 []⟩ := by
  have H (word : List Bool) (v : Fin 3) : tick^[word.length+1]
      (⟨some 7,v,Function.update W 26 word⟩ : Config) =
        ⟨some (addLabel (BinaryModAddMachine.subLabel 0 0)),0,Function.update W 26 []⟩ := by
    induction word generalizing v with
    | nil => simp [tick,TM2ReturnLink.tick,program,step,stepAux,enter,BinaryModuloCode.memory]
    | cons b word ih =>
      have hs : tick (⟨some 7,v,Function.update W 26 (b::word)⟩ : Config) =
          ⟨some 7,BinaryModuloCode.memory (some b),Function.update W 26 word⟩ := by
        cases b <;> simp [tick,TM2ReturnLink.tick,program,step,stepAux,BinaryModuloCode.memory]
      rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,hs]
      exact ih _
  simpa only [Function.update_eq_self] using H (W 26) 0

private theorem step3 (W : Fin 58 → List Bool) (h : W 51 = []) :
    tick (⟨some 3,0,W⟩ : Config) = ⟨some 27,0,Function.update W 51 [false]⟩ := by
  simp [tick,TM2ReturnLink.tick,program,step,stepAux,enter,h]
private theorem step4 (W : Fin 58 → List Bool) :
    tick (⟨some 4,2,W⟩ : Config) = ⟨some (copyLabel 0),0,W⟩ := by rfl
private theorem step6 (W : Fin 58 → List Bool) (h : W 23 = []) :
    tick (⟨some 6,2,W⟩ : Config) = ⟨some 7,0,W⟩ := by
  simp [tick,TM2ReturnLink.tick,program,step,stepAux,enter,BinaryModuloCode.memory,h]
private theorem step8 (W : Fin 58 → List Bool) :
    tick (⟨some 8,2,W⟩ : Config) = ⟨some (writerLabel (CacheRoutineCode.writerLabels .digits)),0,W⟩ := by rfl
private theorem step9 (W : Fin 58 → List Bool) :
    tick (⟨some 9,2,W⟩ : Config) = ⟨some (transferLabel true 0),0,W⟩ := by rfl
private theorem step10 (W : Fin 58 → List Bool) :
    tick (⟨some 10,0,W⟩ : Config) = ⟨some 27,0,W⟩ := by rfl

private theorem stale_bound (W : Fin 58 → List Bool) (N : Nat) (hN : ∀ k,(W k).length ≤ N) :
    (∑ j : Fin 15, ((W (stalePorts j)).length+1)) ≤ 15*N+15 := by
  calc
    _ ≤ ∑ _j : Fin 15, (N+1) := Finset.sum_le_sum (fun j _ => Nat.add_le_add_right (hN _) 1)
    _ = _ := by simp; omega
private theorem final_bound (W : Fin 58 → List Bool) (N Q : Nat)
    (h : ∀ j : Fin 8,(W (finalPorts j)).length ≤ N+Q) :
    (∑ j : Fin 8, ((W (finalPorts j)).length+1)) ≤ 8*N+8*Q+8 := by
  calc
    _ ≤ ∑ _j : Fin 8, (N+Q+1) := Finset.sum_le_sum (fun j _ => Nat.add_le_add_right (h j) 1)
    _ = _ := by simp; omega

theorem used_run (total : Bool) (q r1 r2 N : Nat) (hr1 : r1 < q) (hr2 : r2 < q)
    (vote : Bool) (W : Fin 58 → List Bool)
    (h2 : W 2 = q.bits) (h20 : W 20 = uniformNatEncode r1) (h21 : W 21 = uniformNatEncode r2)
    (h18 : W 18 = [vote]) (hw : ∀ j : Fin 7,W ⟨23+j.val,by omega⟩ = [])
    (h37 : W 37 = []) (hN : ∀ k,(W k).length ≤ N) :
    ∃ used ≤ clock q N,
      tick^[used] (start total W) =
      result W (uniformNatEncode (if total then (r1+r2)%q else r2))
        (if total then [vote] else [false]) := by
  let B := base W
  have hBwork (j : Fin 7) : B ⟨23+j.val,by omega⟩ = [] := by fin_cases j <;> exact hw _
  have hB2 : B 2 = q.bits := h2
  have hB20 : B 20 = uniformNatEncode r1 := h20
  have hB21 : B 21 = uniformNatEncode r2 := h21
  have hB18 : B 18 = [vote] := h18
  have hstale := stale_bound W N hN
  have hR1 : r1.size ≤ (q-1).size := Nat.size_le_size (by omega)
  have hR2 : r2.size ≤ (q-1).size := Nat.size_le_size (by omega)
  have hcomp : (q-r2).size ≤ q.size := Nat.size_le_size (Nat.sub_le _ _)
  cases total with
  | false =>
    have hs := setup_run false W h37
    obtain ⟨u,hu,ht⟩ := transfer_run false B (hBwork 0)
    change _ ≤ (B 50).length+2*(B 21).length+4 at hu
    change tick^[u] (⟨some (transferLabel false 0),0,B⟩ : Config) =
      ⟨some 3,0,Function.update B 50 (B 21)⟩ at ht
    rw [hB21] at ht
    let C := Function.update B 50 (uniformNatEncode r2)
    let D := Function.update C 51 [false]
    have hv : tick^[1] (⟨some 3,0,C⟩ : Config) = ⟨some 27,0,D⟩ := step3 C rfl
    have hf := final_clear_run D
    have hfb := final_bound D N q.size (fun j => by
      fin_cases j
      · exact (hN 2).trans (Nat.le_add_right _ _)
      · exact (hN 23).trans (Nat.le_add_right _ _)
      · exact (hN 24).trans (Nat.le_add_right _ _)
      · exact (hN 25).trans (Nat.le_add_right _ _)
      · exact (hN 26).trans (Nat.le_add_right _ _)
      · exact (hN 27).trans (Nat.le_add_right _ _)
      · exact (hN 28).trans (Nat.le_add_right _ _)
      · exact (hN 29).trans (Nat.le_add_right _ _))
    have he := sequence hs (sequence ht (sequence hv hf))
    have ho : finalCleared D = resultWords W (uniformNatEncode r2) [false] := by
      funext k
      fin_cases k <;> rfl
    change tick^[_] (start false W) = ⟨none,2,finalCleared D⟩ at he
    rw [ho] at he
    refine ⟨_,?_,he⟩
    have hu' : u ≤ 2*N+4 := by
      have hh := hN 21
      change u ≤ 0+2*(W 21).length+4 at hu
      omega
    unfold clock
    omega
  | true =>
    have hs := setup_run true W h37
    obtain ⟨u0,hu0,hc⟩ := complement_phase q r2 hr2 B hB2 hB21 hBwork
    let C := complementAfter B q r2
    have h4 : tick^[1] (⟨some 4,2,C⟩ : Config) = ⟨some (copyLabel 0),0,C⟩ := step4 C
    obtain ⟨u1,hu1,hcopy⟩ := copy_phase (uniformNatEncode r1) C hB20 rfl rfl
    let D := Function.update C 23 (uniformNatEncode r1)
    obtain ⟨u2,hu2,hparse⟩ := parse_phase r1 D rfl rfl rfl rfl
    let E := Function.update (Function.update D 23 []) 27 r1.bits
    have h6 : tick^[1] (⟨some 6,2,E⟩ : Config) = ⟨some 7,0,E⟩ := step6 E rfl
    have hclear := clear26_run E
    let F := Function.update E 26 []
    obtain ⟨u3,hu3,hadd⟩ := add_phase q r1 r2 hr1 hr2 F rfl rfl hB2 rfl rfl rfl rfl rfl
    let z := (r1+r2)%q
    let G := Function.update F 27 z.bits
    have h8 : tick^[1] (⟨some 8,2,G⟩ : Config) =
        ⟨some (writerLabel (CacheRoutineCode.writerLabels .digits)),0,G⟩ := step8 G
    obtain ⟨u4,hu4,hwrite⟩ := writer_phase z G rfl rfl rfl rfl rfl
    let H := Function.update (Function.update G 27 []) 50 (uniformNatEncode z)
    have h9 : tick^[1] (⟨some 9,2,H⟩ : Config) = ⟨some (transferLabel true 0),0,H⟩ := step9 H
    obtain ⟨u5,hu5,hvote⟩ := transfer_run true H rfl
    change tick^[u5] (⟨some (transferLabel true 0),0,H⟩ : Config) =
      ⟨some 10,0,Function.update H 51 (H 18)⟩ at hvote
    have hH18 : H 18 = [vote] := h18
    rw [hH18] at hvote
    let I := Function.update H 51 [vote]
    have h10 : tick^[1] (⟨some 10,0,I⟩ : Config) = ⟨some 27,0,I⟩ := step10 I
    have hfinal := final_clear_run I
    have hfb := final_bound I N q.size (fun j => by
      fin_cases j
      · exact (hN 2).trans (Nat.le_add_right _ _)
      · change 0 ≤ _; omega
      · change 0 ≤ _; omega
      · change 0 ≤ _; omega
      · change 0 ≤ _; omega
      · change 0 ≤ _; omega
      · change (q-r2).bits.length ≤ _; rw [Nat.size_eq_bits_len]; omega
      · change 0 ≤ _; omega)
    have he := sequence hs (sequence hc (sequence h4 (sequence hcopy (sequence hparse
      (sequence h6 (sequence hclear (sequence hadd (sequence h8 (sequence hwrite
        (sequence h9 (sequence hvote (sequence h10 hfinal))))))))))))
    have ho : finalCleared I = resultWords W (uniformNatEncode z) [vote] := by
      funext k
      fin_cases k <;> rfl
    change tick^[_] (start true W) = ⟨none,2,finalCleared I⟩ at he
    rw [ho] at he
    refine ⟨_,?_,he⟩
    have hu1' : u1 ≤ 2*N+2 := by
      have hh := hN 20
      rw [h20] at hh
      omega
    have hu5' : u5 ≤ 2*N+4 := by
      change u5 ≤ 0+2*(W 18).length+4 at hu5
      have hh := hN 18
      omega
    have hz : z.size ≤ (q-1).size := Nat.size_le_size (by have := Nat.mod_lt (r1+r2) (by omega : 0<q); dsimp [z]; omega)
    have hE26 : (E 26).length = r2.size := Nat.size_eq_bits_len r2
    rw [hE26]
    unfold clock
    omega

/-- Pad only the final halt established by the composed execution. -/
theorem padded_run (total : Bool) (q r1 r2 N : Nat) (hr1 : r1 < q) (hr2 : r2 < q)
    (vote : Bool) (W : Fin 58 → List Bool)
    (h2 : W 2 = q.bits) (h20 : W 20 = uniformNatEncode r1) (h21 : W 21 = uniformNatEncode r2)
    (h18 : W 18 = [vote]) (hw : ∀ j : Fin 7,W ⟨23+j.val,by omega⟩ = [])
    (h37 : W 37 = []) (hN : ∀ k,(W k).length ≤ N) :
    tick^[clock q N] (start total W) =
      result W (uniformNatEncode (if total then (r1+r2)%q else r2))
        (if total then [vote] else [false]) := by
  obtain ⟨u,hu,he⟩ := used_run total q r1 r2 N hr1 hr2 vote W h2 h20 h21 h18 hw h37 hN
  obtain ⟨extra,hclock⟩ := Nat.exists_eq_add_of_le hu
  rw [hclock,Nat.add_comm u extra,Function.iterate_add_apply,he]
  exact Function.iterate_fixed (by rfl) extra

theorem local_cost (l : Fin size) : BitOracleMachine.localCost (program l) ≤ 32 := by
  fin_cases l <;> decide +kernel

/-- Actual charged execution, deriving every component cost from the code and
concrete entry records. Original proofs/current state are retained literally. -/
theorem charged_bounded (total : Bool) (q r1 r2 N : Nat) (hr1 : r1 < q) (hr2 : r2 < q)
    (vote : Bool) (W : Fin 58 → List Bool)
    (h2 : W 2 = q.bits) (h20 : W 20 = uniformNatEncode r1) (h21 : W 21 = uniformNatEncode r2)
    (h18 : W 18 = [vote]) (hw : ∀ j : Fin 7,W ⟨23+j.val,by omega⟩ = [])
    (h37 : W 37 = []) (hN : ∀ k,(W k).length ≤ N) :
    ∃ charge ≤ cost q N,
      BitOracleMachine.run code (clock q N) (start total W) =
      pure (result W (uniformNatEncode (if total then (r1+r2)%q else r2))
        (if total then [vote] else [false]),charge) := by
  obtain ⟨charge,hc,he⟩ := BitOracleMachine.compute_run_cost program 32 local_cost (clock q N) (start total W)
  change BitOracleMachine.run code (clock q N) (start total W) =
    pure (tick^[clock q N] (start total W),charge) at he
  rw [padded_run total q r1 r2 N hr1 hr2 vote W h2 h20 h21 h18 hw h37 hN] at he
  exact ⟨charge,hc,he⟩

def inputSize (W : Fin 58 → List Bool) : Nat := Finset.univ.sup (fun k => (W k).length)
theorem inputSize_bound (W : Fin 58 → List Bool) (k : Fin 58) : (W k).length ≤ inputSize W :=
  Finset.le_sup (f := fun k => (W k).length) (Finset.mem_univ k)

/-- The size cap is calculated from the actual resident words. -/
theorem charged (total : Bool) (q r1 r2 : Nat) (hr1 : r1 < q) (hr2 : r2 < q)
    (vote : Bool) (W : Fin 58 → List Bool)
    (h2 : W 2 = q.bits) (h20 : W 20 = uniformNatEncode r1) (h21 : W 21 = uniformNatEncode r2)
    (h18 : W 18 = [vote]) (hw : ∀ j : Fin 7,W ⟨23+j.val,by omega⟩ = [])
    (h37 : W 37 = []) :
    ∃ charge ≤ cost q (inputSize W),
      BitOracleMachine.run code (clock q (inputSize W)) (start total W) =
      pure (result W (uniformNatEncode (if total then (r1+r2)%q else r2))
        (if total then [vote] else [false]),charge) :=
  charged_bounded total q r1 r2 (inputSize W) hr1 hr2 vote W h2 h20 h21 h18 hw h37 (inputSize_bound W)

#print axioms used_run
#print axioms padded_run
#print axioms local_cost
#print axioms charged_bounded
#print axioms inputSize_bound
#print axioms charged
end ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry

namespace ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry.Controls
open OracleComp
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
attribute [local irreducible] BitOracleMachine.run

private def zero_sumInput : Fin 58 → List Bool := ![[true],[false],[true,true],[true],[false,true],[true,false,true],[true,true,true],[false],[false,true],[true,false,true],[false],[false],[false],[false,true],[true,false,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[true],[false,false,true],[true],[],[true],[true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true],[true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,false,true,false],[false],[true],[true,true,false,false,true,true,true,true,true,true,true,true,false,true,true,false,false,true,false,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,false,false,true,false,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true],[true,true,false,false,true,true,true,true,true,true,true,false,true,true,false,true,true,true,true,true,false,false,true,true,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,true,false,true,false,true,true,true,true,false,false,true,true,false,true,false,true,false,true,false,true,true,true,true,true,true,false,true,true,false,true,true,true,true,true,false,false,true,true,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,true,false,true,false,true,true,true,true,false,false,true,true,false,true,false,true,false,true,false],[true,true,false,false,true,true,true,true,true,true,true,true,true,true,false,true,true,false,true,false,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,true,false,true,false,false,false,false,false,false,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,false,true,false,true,true,true,true,true,true,true,true,false,true,true,false,false,false,true,true,true,true,true,false,false,true,true,false,true,true,true,true,true,true,true,true,true,true,false,true,false,false,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,true,true,false,false,true,false,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,false,false,true,false,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,false,true,false],[true,true,false,false,true],[false],[true,true,false,false,true,true,true,true,true,true,true,false,true,true,false,true,true,true,true,true,false,false,true,true,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,true,false,true,false,true,true,true,true,false,false,true,true,false,true,false,true,false,true,false,true,true,true,true,true,true,false,true,true,false,true,true,true,true,true,false,false,true,true,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,true,false,true,false,true,true,true,true,false,false,true,true,false,true,false,true,false,true,false],[],[false,false,true],[false,true],[],[]]
private def zero_sumExpected : Fin 58 → List Bool := ![[true],[],[],[],[false,true],[true,false,true],[true,true,true],[],[false,true],[true,false,true],[],[],[],[],[true,false,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,false,true,false],[false],[true],[true,true,false,false,true,true,true,true,true,true,true,true,false,true,true,false,false,true,false,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,false,false,true,false,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true],[true,true,false,false,true,true,true,true,true,true,true,false,true,true,false,true,true,true,true,true,false,false,true,true,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,true,false,true,false,true,true,true,true,false,false,true,true,false,true,false,true,false,true,false,true,true,true,true,true,true,false,true,true,false,true,true,true,true,true,false,false,true,true,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,true,false,true,false,true,true,true,true,false,false,true,true,false,true,false,true,false,true,false],[],[false],[true],[true,true,false,false,true,true,true,true,true,true,true,false,true,true,false,true,true,true,true,true,false,false,true,true,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,true,false,true,false,true,true,true,true,false,false,true,true,false,true,false,true,false,true,false,true,true,true,true,true,true,false,true,true,false,true,true,true,true,true,false,false,true,true,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,true,false,true,false,true,true,true,true,false,false,true,true,false,true,false,true,false,true,false],[],[false,false,true],[false,true],[],[]]
/-- Full58 endpoint from the independent numeric/record oracle used in the
actual-code gate, instantiated through the proved general execution. -/
theorem zero_sum_execution :
    ∃ charge ≤ cost 3 423,
      BitOracleMachine.run code (clock 3 423) (start true zero_sumInput) =
        pure ((⟨none,2,zero_sumExpected⟩ : Config),charge) := by
  obtain ⟨charge,hc,he⟩ := charged_bounded true 3 1 2 423 (by decide) (by decide) true zero_sumInput
    rfl rfl rfl rfl (by intro j; fin_cases j <;> rfl) rfl
    (by intro k; fin_cases k <;> decide +kernel)
  have ho : result zero_sumInput (uniformNatEncode 0) [true] =
      (⟨none,2,zero_sumExpected⟩ : Config) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨charge,hc,he.trans (congrArg (fun cfg => pure (cfg,charge)) ho)⟩
#print axioms zero_sum_execution

private def second_nonceInput : Fin 58 → List Bool := ![[true],[false],[true,true],[true],[false,true],[true,false,true],[true,true,true],[false],[false,true],[true,false,true],[false],[false],[false],[true],[true,false,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[true],[false,false,true],[true],[],[true],[true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true],[true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,false,true,false],[false],[true],[true,true,false,false,true,true,true,true,true,true,true,true,false,true,true,false,false,true,false,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,false,false,true,false,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true],[true,true,false,false,true,true,true,true,true,true,true,false,true,true,false,true,true,true,true,true,false,false,true,true,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,true,false,true,false,true,true,true,true,false,false,true,true,false,true,false,true,false,true,false,true,true,true,true,true,true,false,true,true,false,true,true,true,true,true,false,false,true,true,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,true,false,true,false,true,true,true,true,false,false,true,true,false,true,false,true,false,true,false],[true,true,false,false,true,true,true,true,true,true,true,true,true,true,false,true,true,false,true,false,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,true,false,true,false,false,false,false,false,false,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,false,true,false,true,true,true,true,true,true,true,true,false,true,true,false,false,false,true,true,true,true,true,false,false,true,true,false,true,true,true,true,true,true,true,true,true,true,false,true,false,false,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,true,true,false,false,true,false,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,false,false,true,false,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,false,true,false],[],[],[],[],[],[],[],[]]
private def second_nonceExpected : Fin 58 → List Bool := ![[true],[],[],[],[false,true],[true,false,true],[true,true,true],[],[false,true],[true,false,true],[],[],[],[],[true,false,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,false,true,false],[false],[true],[true,true,false,false,true,true,true,true,true,true,true,true,false,true,true,false,false,true,false,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,false,false,true,false,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true],[true,true,false,false,true,true,true,true,true,true,true,false,true,true,false,true,true,true,true,true,false,false,true,true,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,true,false,true,false,true,true,true,true,false,false,true,true,false,true,false,true,false,true,false,true,true,true,true,true,true,false,true,true,false,true,true,true,true,true,false,false,true,true,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,true,false,true,false,true,true,true,true,false,false,true,true,false,true,false,true,false,true,false],[],[true,true,false,false,true],[false],[],[],[],[],[],[]]
/-- Full58 endpoint from the independent numeric/record oracle used in the
actual-code gate, instantiated through the proved general execution. -/
theorem second_nonce_execution :
    ∃ charge ≤ cost 3 423,
      BitOracleMachine.run code (clock 3 423) (start false second_nonceInput) =
        pure ((⟨none,2,second_nonceExpected⟩ : Config),charge) := by
  obtain ⟨charge,hc,he⟩ := charged_bounded false 3 1 2 423 (by decide) (by decide) true second_nonceInput
    rfl rfl rfl rfl (by intro j; fin_cases j <;> rfl) rfl
    (by intro k; fin_cases k <;> decide +kernel)
  have ho : result second_nonceInput (uniformNatEncode 2) [false] =
      (⟨none,2,second_nonceExpected⟩ : Config) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨charge,hc,he.trans (congrArg (fun cfg => pure (cfg,charge)) ho)⟩
#print axioms second_nonce_execution
end ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry.Controls

namespace ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry.Controls
/-- Correct .digits entry uses the counter, so one is encoded as U1. -/
theorem correct_counter_one : FrameWriteMachine.tick^[6]
    (FrameWriteMachine.state (some .digits) [] [] [] [] [true] none) =
    FrameWriteMachine.state none [] [] [] [true,false,true] [] (some true) :=
  FrameWriteMachine.prefix_run 1 [] none
/-- The rejected layout put digits on input instead of counter. Its actual
three-step execution encodes zero and leaves the intended one untouched. -/
theorem wrong_input_one : FrameWriteMachine.tick^[3]
    (FrameWriteMachine.state (some .digits) [true] [] [] [] [] none) =
    FrameWriteMachine.state none [true] [] [] [false] [] (some true) := by
  simp [FrameWriteMachine.tick,FrameWriteMachine.state,FrameWriteMachine.program,Turing.TM2.stepAux,Function.iterate_succ_apply]
  funext k
  rcases k with (k|⟨⟩)
  · cases k <;> rfl
  · rfl

theorem wrong_input_not_one :
    ((FrameWriteMachine.tick^[3])
      (FrameWriteMachine.state (some .digits) [true] [] [] [] [] none)).stk FrameWriteMachine.output ≠
      uniformNatEncode 1 := by rw [wrong_input_one]; decide
#print axioms correct_counter_one
#print axioms wrong_input_one
#print axioms wrong_input_not_one
end ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry.Controls
