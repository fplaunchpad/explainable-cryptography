import ExplainableCrypto.Helios.Computational.NativeOracleTape
import Mathlib.Tactic.FinCases

/-! Mechanical translation for the bounded native feasibility experiment.
Six dense word stacks represent the three native before/right tape halves.
Blank writes and moves requiring storage of a blank cell are explicitly rejected;
no coverage claim is made for those commands. Native selection is frozen in a
finite label before any of the three selected actions executes. -/
namespace ExplainableCrypto.Helios.Computational.NativeWordCompiler
open Turing OracleComp OracleSpec
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

abbrev size (l : Nat) := 55*l
abbrev Config (l : Nat) := BitOracleMachine.Config 6 (size l) 27
abbrev Statement (l : Nat) := TM2.Stmt (fun _ : Fin 6 => Bool) (Fin (size l)) (Fin 27)

def cellCode : Option Bool → Nat
  | none => 0
  | some false => 1
  | some true => 2

theorem cellCode_lt (b : Option Bool) : cellCode b < 3 := by
  cases b with
  | none => decide
  | some b => cases b <;> decide

def cell (n : Nat) : Option Bool := if n = 0 then none else some (n == 2)
def heads (v : Fin 27) : Fin 3 → Option Bool :=
  ![cell (v.val%3),cell ((v.val/3)%3),cell (v.val/9)]
def encodeHeads (h : Fin 3 → Option Bool) : Fin 27 :=
  ⟨cellCode (h 0)+3*cellCode (h 1)+9*cellCode (h 2),by
    have := cellCode_lt (h 0); have := cellCode_lt (h 1); have := cellCode_lt (h 2); omega⟩

theorem heads_encode (h : Fin 3 → Option Bool) : heads (encodeHeads h) = h := by
  funext i
  generalize h0 : h 0 = a
  generalize h1 : h 1 = b
  generalize h2 : h 2 = c
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases i <;> simp [heads,encodeHeads,cellCode,cell,h0,h1,h2]

def entryLabel {l : Nat} (q : Fin l) : Fin (size l) := ⟨q.val,by have := q.isLt; dsimp [size]; omega⟩
def commandLabel {l : Nat} (q : Fin l) (v : Fin 27) : Fin (size l) :=
  ⟨l+27*q.val+v.val,by have := q.isLt; have := v.isLt; dsimp [size]; omega⟩
def eventLabel {l : Nat} (q : Fin l) (v : Fin 27) : Fin (size l) :=
  ⟨28*l+27*q.val+v.val,by have := q.isLt; have := v.isLt; dsimp [size]; omega⟩
def leftPort (i : Fin 3) : Fin 6 := ⟨2*i.val,by have := i.isLt; omega⟩
def rightPort (i : Fin 3) : Fin 6 := ⟨2*i.val+1,by have := i.isLt; omega⟩

def head0 (_ : Fin 27) (b : Option Bool) : Fin 27 :=
  ⟨cellCode b,by have := cellCode_lt b; omega⟩
def head1 (v : Fin 27) (b : Option Bool) : Fin 27 :=
  ⟨v.val%3+3*cellCode b,by have := cellCode_lt b; omega⟩
def head2 (v : Fin 27) (b : Option Bool) : Fin 27 :=
  ⟨v.val%9+9*cellCode b,by have := cellCode_lt b; omega⟩

/-- Memory 26 at halt marks an unsupported dense-word action. -/
def unsupported {l : Nat} : Statement l := .load (fun _ => 26) .halt

def action {l : Nat} (i : Fin 3) (a : Option (TM0.Stmt (Option Bool)))
    (next : Statement l) : Statement l :=
  match a with
  | none => next
  | some (.write none) => unsupported
  | some (.write (some b)) =>
      .pop (rightPort i) (fun v _ => v) (.push (rightPort i) (fun _ => b) next)
  | some (.move .right) =>
      .pop (rightPort i) head0
        (.branch (fun v => v != 0) (.push (leftPort i) (fun v => v == 2) next) unsupported)
  | some (.move .left) =>
      .pop (leftPort i) head0
        (.branch (fun v => v != 0) (.push (rightPort i) (fun v => v == 2) next) unsupported)

def localProgram {l : Nat} (next : Fin l) (acts : Fin 3 → Option (TM0.Stmt (Option Bool))) : Statement l :=
  action 0 (acts 0) (action 1 (acts 1) (action 2 (acts 2)
    (.load (fun _ => 0) (.goto (fun _ => entryLabel next)))))

/-- All three actual heads are read before native-code selection. -/
def entry {l : Nat} (q : Fin l) : Statement l :=
  .peek 1 head0 (.peek 3 head1 (.peek 5 head2 (.goto (commandLabel q))))

/-- Clearing the old answer's left half preserves the frozen native choice. -/
def command {l : Nat} (native : NativeOracleTape.Code l) (q : Fin l) (v : Fin 27) :
    BitOracleMachine.Command 6 (size l) 27 :=
  match native q (heads v) with
  | .halt => .compute (.load (fun _ => 0) .halt)
  | .local next acts => .compute (localProgram next acts)
  | .oracle _ _ => .compute (.pop 4 head0
      (.branch (fun x => x == 0) (.goto (fun _ => eventLabel q v))
        (.goto (fun _ => commandLabel q v))))

def event {l : Nat} (native : NativeOracleTape.Code l) (q : Fin l) (v : Fin 27) :
    BitOracleMachine.Command 6 (size l) 27 :=
  match native q (heads v) with
  | .oracle .hash next => .hash 3 5 (entryLabel next)
  | .oracle .coin next => .coin 5 (entryLabel next)
  | _ => .compute unsupported

/-- The generated code is a function of the native transition table alone. -/
def code {l : Nat} (native : NativeOracleTape.Code l) (k : Fin (size l)) :
    BitOracleMachine.Command 6 (size l) 27 :=
  if h0 : k.val < l then .compute (entry ⟨k.val,h0⟩)
  else if h1 : k.val < 28*l then
    command native ⟨(k.val-l)/27,by have := k.isLt; dsimp [size] at *; omega⟩
      ⟨(k.val-l)%27,by omega⟩
  else event native ⟨(k.val-28*l)/27,by have := k.isLt; dsimp [size] at *; omega⟩
      ⟨(k.val-28*l)%27,by omega⟩

theorem code_entry {l : Nat} (native : NativeOracleTape.Code l) (q : Fin l) :
    code native (entryLabel q) = .compute (entry q) := by
  unfold code
  split
  · rfl
  · rename_i h
    have := q.isLt
    simp only [entryLabel] at h
    omega

theorem code_command {l : Nat} (native : NativeOracleTape.Code l) (q : Fin l) (v : Fin 27) :
    code native (commandLabel q v) = command native q v := by
  unfold code
  split
  · rename_i h
    simp only [commandLabel] at h
    omega
  · split
    · congr 1 <;> apply Fin.ext <;> dsimp [commandLabel] <;> have := v.isLt <;> omega
    · rename_i h0 h1
      have := q.isLt
      have := v.isLt
      simp only [commandLabel] at h1
      omega

theorem code_event {l : Nat} (native : NativeOracleTape.Code l) (q : Fin l) (v : Fin 27) :
    code native (eventLabel q v) = event native q v := by
  unfold code
  split
  · rename_i h
    simp only [eventLabel] at h
    omega
  · split
    · rename_i h0 h1
      simp only [eventLabel] at h1
      omega
    · congr 1 <;> apply Fin.ext <;> dsimp [eventLabel] <;> have := v.isLt <;> omega

def tape (before right : List Bool) : Tape (Option Bool) :=
  Tape.mk' (ListBlank.mk (before.map some)) (ListBlank.mk (right.map some))
def nativeConfig {l : Nat} (label : Option (Fin l)) (words : Fin 6 → List Bool) : NativeOracleTape.Config l :=
  ⟨label,tape (words 0) (words 1),tape (words 2) (words 3),tape (words 4) (words 5)⟩
def present {l : Nat} (label : Option (Fin l)) (words : Fin 6 → List Bool) : Config l :=
  ⟨label.map entryLabel,0,words⟩
def start {l : Nat} (label : Fin l) (words : Fin 6 → List Bool) : Config l := present (some label) words

def snapshot (ws : Fin 6 → List Bool) : Fin 27 :=
  head2 (head1 (head0 0 (ws 1).head?) (ws 3).head?) (ws 5).head?

theorem entry_step {l : Nat} (native : NativeOracleTape.Code l) (q : Fin l)
    (ws : Fin 6 → List Bool) :
    BitOracleMachine.step (code native) (present (some q) ws) =
      pure (⟨some (commandLabel q (snapshot ws)),snapshot ws,ws⟩,4) := by
  simp only [BitOracleMachine.step,present,Option.map_some,code_entry]
  rfl

/-- Exact explicit boundary of the dense-word action representation. -/
def ActionSupported (before right : List Bool) : Option (TM0.Stmt (Option Bool)) → Prop
  | none => True
  | some (.write (some _)) => True
  | some (.write none) => False
  | some (.move .left) => before ≠ []
  | some (.move .right) => right ≠ []

end ExplainableCrypto.Helios.Computational.NativeWordCompiler
