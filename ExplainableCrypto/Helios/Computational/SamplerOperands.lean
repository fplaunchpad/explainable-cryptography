import ExplainableCrypto.Helios.Computational.BitIncrementMachine
import ExplainableCrypto.Helios.Computational.TM2StackFrame
import ExplainableCrypto.Helios.Computational.CoinScalarMachine

/-! Serialized sampler input: unary slack, false delimiter, original natural
prefix. Direct entry uses a positive modulus; uniform entry executes t+1 for
the original inclusive upper bound. No input-dependent host arithmetic runs. -/
namespace ExplainableCrypto.Helios.Computational.SamplerOperands
open Turing.TM2

inductive Label where
  | slack (uniform : Bool) | parse (uniform : Bool) (label : NatPrefixMachine.Label)
  | parsed (uniform : Bool) | increment (phase : Bool) | ready | collect | restore
  deriving DecidableEq

abbrev Config := Cfg (fun _ : Fin 8 => Bool) Label (Option Bool)
abbrev Frame := Fin 3 → List Bool

/-- Shared parser/counter ports; extra ports retain width and three saved words. -/
def layout : NatPrefixMachine.Stack ⊕ Fin 4 ≃ Fin 8 where
  toFun
    | .inl .input => 4 | .inl .count => 0 | .inl .scratch => 3 | .inl .output => 1
    | .inr k => ![2,5,6,7] k
  invFun := ![.inl .count,.inl .output,.inr 0,.inl .scratch,.inl .input,.inr 1,.inr 2,.inr 3]
  left_inv k := by cases k with
    | inl k => cases k <;> rfl
    | inr k => fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

private def fail : Stmt (fun _ : Fin 8 => Bool) Label (Option Bool) :=
  .load (fun _ => some false) .halt

def program : Label → Stmt (fun _ : Fin 8 => Bool) Label (Option Bool)
  | .slack mode => .pop 4 (fun _ b => b) <| .branch Option.isSome
      (.branch (fun b => b.getD false)
        (.push 2 (fun _ => true) (.goto (fun _ => .slack mode)))
        (.goto (fun _ => .parse mode .width))) fail
  | .parse mode l => TM2ReturnLink.redirect (.parse mode) (.parsed mode)
      (TM2StackFrame.relocate layout (NatPrefixMachine.program l))
  | .parsed mode => .branch (fun b => b == some true)
      (.goto (fun _ => if mode then .increment false else .ready)) fail
  | .increment b => TM2ReturnLink.redirect .increment .ready
      (TM2StackFrame.relocate layout (BitIncrementMachine.program b))
  | .ready => .peek 1 (fun _ b => b) <| .branch Option.isSome
      (.goto (fun _ => .collect)) fail
  | .collect => .pop 1 (fun _ b => b) <| .branch Option.isSome
      (.push 3 (fun b => b.getD false)
        (.push 2 (fun _ => true) (.goto (fun _ => .collect))))
      (.goto (fun _ => .restore))
  | .restore => .pop 3 (fun _ b => b) <| .branch Option.isSome
      (.push 1 (fun b => b.getD false) (.goto (fun _ => .restore)))
      (.load (fun _ => none) .halt)

def tick (cfg : Config) : Config := (step program cfg).getD cfg

def state (phase : Option Label) (input modulus width count temp : List Bool)
    (frame : Frame) (v : Option Bool) : Config :=
  ⟨phase,v,![count,modulus,width,temp,input,frame 0,frame 1,frame 2]⟩

def input (slack n : Nat) (suffix : List Bool) : List Bool :=
  List.replicate slack true ++ false :: (uniformNatEncode n ++ suffix)

def start (mode : Bool) (word : List Bool) (frame : Frame) : Config :=
  state (some (.slack mode)) word [] [] [] [] frame none

def result (slack q : Nat) (suffix : List Bool) (frame : Frame) : Config :=
  state none suffix q.bits (List.replicate (q.size+slack) true) [] [] frame none

private theorem slack_run (mode : Bool) (n : Nat) (word width : List Bool)
    (frame : Frame) (v : Option Bool) :
    tick^[n+1] (state (some (.slack mode)) (List.replicate n true ++ false::word)
      [] width [] [] frame v) =
      state (some (.parse mode .width)) word [] (List.replicate n true ++ width) [] [] frame (some false) := by
  induction n generalizing width v with
  | zero =>
    simp [tick,state,program,stepAux]
    funext k; fin_cases k <;> rfl
  | succ n ih =>
    have hs : tick (state (some (.slack mode))
        (true::(List.replicate n true ++ false::word)) [] width [] [] frame v) =
        state (some (.slack mode)) (List.replicate n true ++ false::word)
          [] (true::width) [] [] frame (some true) := by
      simp [tick,state,program,stepAux]
      funext k; fin_cases k <;> rfl
    rw [List.replicate_succ,List.cons_append,Function.iterate_succ_apply,hs,ih]
    have he : List.replicate n true ++ true::width =
        true::(List.replicate n true ++ width) := by
      calc
        _ = (List.replicate n true ++ [true]) ++ width := by simp
        _ = List.replicate (n+1) true ++ width := by rw [List.replicate_succ']
        _ = _ := by rw [List.replicate_succ,List.cons_append]
    rw [he,List.cons_append]

private def parserFrame (width : List Bool) (frame : Frame) : Fin 4 → List Bool :=
  ![width,frame 0,frame 1,frame 2]

private theorem parse_run (mode : Bool) (n : Nat) (suffix width : List Bool) (frame : Frame) :
    ∃ used ≤ 3*n.size+3,
      tick^[used] (state (some (.parse mode .width)) (uniformNatEncode n ++ suffix)
        [] width [] [] frame (some false)) =
      state (some (.parsed mode)) suffix n.bits width [] [] frame (some true) := by
  let c := NatPrefixMachine.config (some .width) (uniformNatEncode n++suffix) [] [] [] (some false)
  have hstart : NatPrefixMachine.tick c = NatPrefixMachine.tick (NatPrefixMachine.start (uniformNatEncode n++suffix)) := rfl
  have hr : NatPrefixMachine.tick^[3*n.size+3] c =
      NatPrefixMachine.config none suffix [] [] n.bits (some true) := by
    rw [Function.iterate_succ_apply,hstart,← Function.iterate_succ_apply]
    exact NatPrefixMachine.encoded_run n suffix
  have he := TM2StackFrame.run layout NatPrefixMachine.program (3*n.size+3) c (parserFrame width frame)
  change (TM2ReturnLink.tick (fun l => TM2StackFrame.relocate layout (NatPrefixMachine.program l)))^[3*n.size+3]
    (TM2StackFrame.embed layout c (parserFrame width frame)) = _ at he
  change _ = TM2StackFrame.embed layout (NatPrefixMachine.tick^[3*n.size+3] c) (parserFrame width frame) at he
  rw [hr] at he
  obtain ⟨u,hu,hh⟩ := TM2ReturnLink.run
    (fun l => TM2StackFrame.relocate layout (NatPrefixMachine.program l)) program
    (.parse mode) (.parsed mode) (fun _ => rfl) (3*n.size+3)
    (TM2StackFrame.embed layout c (parserFrame width frame)) (by rw [he]; rfl)
  rw [he] at hh
  refine ⟨u,hu,?_⟩
  have ha : TM2ReturnLink.embed (.parse mode) (.parsed mode)
      (TM2StackFrame.embed layout c (parserFrame width frame)) =
      state (some (.parse mode .width)) (uniformNatEncode n++suffix) [] width [] [] frame (some false) := by
    apply congrArg (Cfg.mk _ _); funext k; fin_cases k <;> rfl
  have hb : TM2ReturnLink.embed (.parse mode) (.parsed mode)
      (TM2StackFrame.embed layout (NatPrefixMachine.config none suffix [] [] n.bits (some true))
        (parserFrame width frame)) = state (some (.parsed mode)) suffix n.bits width [] [] frame (some true) := by
    apply congrArg (Cfg.mk _ _); funext k; fin_cases k <;> rfl
  rw [ha,hb] at hh
  exact hh

private theorem collect_run (bits temp width suffix : List Bool) (frame : Frame) (v : Option Bool) :
    tick^[bits.length+1] (state (some .collect) suffix bits width [] temp frame v) =
      state (some .restore) suffix [] (List.replicate bits.length true ++ width) []
        (bits.reverse++temp) frame none := by
  induction bits generalizing temp width v with
  | nil => simp [tick,state,program,stepAux]
  | cons b bits ih =>
    have hs : tick (state (some .collect) suffix (b::bits) width [] temp frame v) =
        state (some .collect) suffix bits (true::width) [] (b::temp) frame (some b) := by
      simp [tick,state,program,stepAux]
      funext k; fin_cases k <;> rfl
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,hs,ih]
    simp [List.replicate_succ',List.append_assoc]

private theorem restore_run (bits temp width suffix : List Bool) (frame : Frame) (v : Option Bool) :
    tick^[temp.length+1] (state (some .restore) suffix bits width [] temp frame v) =
      state none suffix (temp.reverse++bits) width [] [] frame none := by
  induction temp generalizing bits v with
  | nil => simp [tick,state,program,stepAux]
  | cons b temp ih =>
    have hs : tick (state (some .restore) suffix bits width [] (b::temp) frame v) =
        state (some .restore) suffix (b::bits) width [] temp frame (some b) := by
      simp [tick,state,program,stepAux]
      funext k; fin_cases k <;> rfl
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,hs,ih]
    simp

/-- The unchanged width-collection region, from already loaded canonical digits. -/
theorem ready_run (slack q : Nat) (hq : 0 < q) (suffix : List Bool) (frame : Frame)
    (v : Option Bool) :
    tick^[2*q.size+3] (state (some .ready) suffix q.bits (List.replicate slack true) [] [] frame v) =
      result slack q suffix frame := by
  have hbits : q.bits ≠ [] := by
    intro h
    have := congrArg bitsValue h
    rw [bitsValue_bits] at this
    change q = 0 at this
    omega
  have hs : tick (state (some .ready) suffix q.bits (List.replicate slack true) [] [] frame v) =
      state (some .collect) suffix q.bits (List.replicate slack true) [] [] frame q.bits.head? := by
    cases hb : q.bits with
    | nil => exact (hbits hb).elim
    | cons b bs => simp [tick,state,program,stepAux]
  rw [show 2*q.size+3 = (q.bits.length+1)+(q.bits.length+1)+1 by rw [←Nat.size_eq_bits_len]; omega,
    Function.iterate_succ_apply,hs,Function.iterate_add_apply,collect_run]
  simpa only [result,List.length_reverse,List.reverse_reverse,List.reverse_nil,List.nil_append,List.append_nil,
    ←Nat.size_eq_bits_len,←List.replicate_add] using
    restore_run [] q.bits.reverse (List.replicate q.bits.length true ++ List.replicate slack true) suffix frame none

private theorem increment_run (n : Nat) (suffix width : List Bool) (frame : Frame) :
    ∃ used ≤ 2*n.size+2,
      tick^[used] (state (some (.increment false)) suffix n.bits width [] [] frame (some true)) =
      state (some .ready) suffix (n+1).bits width [] [] frame (some true) := by
  obtain ⟨u,hu,hr⟩ := BitIncrementMachine.run n suffix [] (some true)
  let c := BitIncrementMachine.config (some false) n.bits [] suffix [] (some true)
  have he := TM2StackFrame.run layout BitIncrementMachine.program u c (parserFrame width frame)
  change (TM2ReturnLink.tick (fun l => TM2StackFrame.relocate layout (BitIncrementMachine.program l)))^[u]
    (TM2StackFrame.embed layout c (parserFrame width frame)) = _ at he
  change _ = TM2StackFrame.embed layout (BitIncrementMachine.tick^[u] c) (parserFrame width frame) at he
  rw [show BitIncrementMachine.tick^[u] c =
      BitIncrementMachine.config none (n+1).bits [] suffix [] (some true) from hr] at he
  obtain ⟨v,hv,hh⟩ := TM2ReturnLink.run
    (fun l => TM2StackFrame.relocate layout (BitIncrementMachine.program l)) program
    .increment .ready (fun _ => rfl) u
    (TM2StackFrame.embed layout c (parserFrame width frame)) (by rw [he]; rfl)
  rw [he] at hh
  refine ⟨v,hv.trans hu,?_⟩
  have ha : TM2ReturnLink.embed .increment .ready
      (TM2StackFrame.embed layout c (parserFrame width frame)) =
      state (some (.increment false)) suffix n.bits width [] [] frame (some true) := by
    apply congrArg (Cfg.mk _ _); funext k; fin_cases k <;> rfl
  have hb : TM2ReturnLink.embed .increment .ready
      (TM2StackFrame.embed layout (BitIncrementMachine.config none (n+1).bits [] suffix [] (some true))
        (parserFrame width frame)) = state (some .ready) suffix (n+1).bits width [] [] frame (some true) := by
    apply congrArg (Cfg.mk _ _); funext k; fin_cases k <;> rfl
  rw [ha,hb] at hh
  exact hh

/-- Direct positive modulus: parsing and width preparation execute, preserving
the full trailing input/private frame and clearing the work ports. -/
theorem run (slack q : Nat) (hq : 0 < q) (suffix : List Bool) (frame : Frame) :
    ∃ used ≤ slack+5*q.size+8,
      tick^[used] (start false (input slack q suffix) frame) = result slack q suffix frame := by
  obtain ⟨u,hu,hr⟩ := parse_run false q suffix (List.replicate slack true) frame
  have hs : tick (state (some (.parsed false)) suffix q.bits (List.replicate slack true) [] [] frame (some true)) =
      state (some .ready) suffix q.bits (List.replicate slack true) [] [] frame (some true) := by
    simp [tick,state,program,stepAux]
  refine ⟨(2*q.size+3)+(1+(u+(slack+1))),by omega,?_⟩
  rw [Function.iterate_add_apply (m := 2*q.size+3),Function.iterate_add_apply (m := 1),
    Function.iterate_add_apply (m := u)]
  unfold start input
  rw [slack_run]
  simp only [List.append_nil]
  rw [hr,Function.iterate_one,hs,ready_run slack q hq]

/-- Original inclusive upper bound t becomes t+1 by actual binary increment,
including t=0 and carry chains; no prepared successor is an input premise. -/
theorem uniform_run (slack t : Nat) (suffix : List Bool) (frame : Frame) :
    ∃ used ≤ slack+5*t.size+2*(t+1).size+10,
      tick^[used] (start true (input slack t suffix) frame) = result slack (t+1) suffix frame := by
  obtain ⟨u,hu,hr⟩ := parse_run true t suffix (List.replicate slack true) frame
  obtain ⟨v,hv,hvRun⟩ := increment_run t suffix (List.replicate slack true) frame
  have hs : tick (state (some (.parsed true)) suffix t.bits (List.replicate slack true) [] [] frame (some true)) =
      state (some (.increment false)) suffix t.bits (List.replicate slack true) [] [] frame (some true) := by
    simp [tick,state,program,stepAux]
  refine ⟨(2*(t+1).size+3)+(v+(1+(u+(slack+1)))),by omega,?_⟩
  rw [Function.iterate_add_apply (m := 2*(t+1).size+3),Function.iterate_add_apply (m := v),
    Function.iterate_add_apply (m := 1),Function.iterate_add_apply (m := u)]
  unfold start input
  rw [slack_run]
  simp only [List.append_nil]
  rw [hr,Function.iterate_one,hs,hvRun,ready_run slack (t+1) (by omega)]

/-- Direct modulus zero reaches explicit failure instead of invoking division. -/
theorem zero_rejected (slack : Nat) (suffix : List Bool) (frame : Frame) :
    ∃ used ≤ slack+6,
      tick^[used] (start false (input slack 0 suffix) frame) =
        state none suffix [] (List.replicate slack true) [] [] frame (some false) := by
  obtain ⟨u,hu,hr⟩ := parse_run false 0 suffix (List.replicate slack true) frame
  refine ⟨2+(u+(slack+1)),by simpa using (show 2+(u+(slack+1)) ≤ slack+6 from by norm_num at hu; omega),?_⟩
  rw [Function.iterate_add_apply (m := 2),Function.iterate_add_apply (m := u)]
  unfold start input
  rw [slack_run]
  simp only [List.append_nil]
  rw [hr]
  rfl

/-- Specification-only range interpretation; executable code uses finite labels. -/
def range (mode : Bool) (n : Nat) : Nat := if mode then n+1 else n

def clock (mode : Bool) (slack n : Nat) : Nat :=
  if mode then slack+5*n.size+2*(n+1).size+10 else slack+5*n.size+8

/-- A fixed analysis clock pads only after the preparation has halted. -/
theorem run_fixed (mode : Bool) (slack n : Nat) (hq : 0 < range mode n)
    (suffix : List Bool) (frame : Frame) :
    tick^[clock mode slack n] (start mode (input slack n suffix) frame) =
      result slack (range mode n) suffix frame := by
  have hr : ∃ used ≤ clock mode slack n,
      tick^[used] (start mode (input slack n suffix) frame) = result slack (range mode n) suffix frame := by
    cases mode with
    | false => exact run slack n hq suffix frame
    | true => exact uniform_run slack n suffix frame
  obtain ⟨u,hu,hr⟩ := hr
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hu
  rw [hd,Nat.add_comm u d,Function.iterate_add_apply,hr]
  exact Function.iterate_fixed (by rfl : tick (result slack (range mode n) suffix frame) = _) d

def labels : Label ≃ Fin 15 where
  toFun
    | .slack false => 0 | .slack true => 1
    | .parse false .width => 2 | .parse false .payload => 3 | .parse false .restore => 4
    | .parse true .width => 5 | .parse true .payload => 6 | .parse true .restore => 7
    | .parsed false => 8 | .parsed true => 9
    | .increment false => 10 | .increment true => 11
    | .ready => 12 | .collect => 13 | .restore => 14
  invFun := ![.slack false,.slack true,.parse false .width,.parse false .payload,.parse false .restore,
    .parse true .width,.parse true .payload,.parse true .restore,.parsed false,.parsed true,
    .increment false,.increment true,.ready,.collect,.restore]
  left_inv l := by
    cases l with
    | slack b | parsed b | increment b => cases b <;> rfl
    | parse b l => cases b <;> cases l <;> rfl
    | ready | collect | restore => rfl
  right_inv k := by fin_cases k <;> rfl

def compiled : Fin 15 → Stmt (fun _ : Fin 8 => Bool) (Fin 15) (Fin 3) :=
  TM2FiniteCoordinates.program (Equiv.refl _) labels BinaryModuloCode.memory program

def present (cfg : Config) : BitOracleMachine.Config 8 15 3 :=
  TM2FiniteCoordinates.present (Equiv.refl _) labels BinaryModuloCode.memory cfg

/-- Fixed local instruction cost includes parsing, carries, guards and copying. -/
theorem local_cost (label : Fin 15) : BitOracleMachine.localCost (compiled label) ≤ 32 := by
  fin_cases label <;> decide +kernel

/-- Preparation executes before any coin query, with its actual complete output
and a derived charge. This includes serial parsing and the uniform successor. -/
theorem charged (mode : Bool) (slack n : Nat) (hq : 0 < range mode n)
    (suffix : List Bool) (frame : Frame) :
    ∃ charge ≤ 32*clock mode slack n,
      BitOracleMachine.run (fun l => .compute (compiled l)) (clock mode slack n)
        (present (start mode (input slack n suffix) frame)) =
          pure (present (result slack (range mode n) suffix frame),charge) := by
  obtain ⟨charge,hc,he⟩ := BitOracleMachine.compute_run_cost compiled 32 local_cost
    (clock mode slack n) (present (start mode (input slack n suffix) frame))
  refine ⟨charge,hc,?_⟩
  rw [compiled,present,TM2FiniteCoordinates.run] at he
  change _ = pure (present (tick^[clock mode slack n] (start mode (input slack n suffix) frame)),charge) at he
  rw [run_fixed mode slack n hq] at he
  exact he

end ExplainableCrypto.Helios.Computational.SamplerOperands
