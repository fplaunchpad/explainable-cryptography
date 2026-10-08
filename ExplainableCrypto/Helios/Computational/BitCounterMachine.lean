import ExplainableCrypto.Helios.Computational.NatPrefixMachine

/-! Concrete canonical binary decrement for the parser's output stack.
The untouched input/count stacks are part of the complete execution theorem. -/
namespace ExplainableCrypto.Helios.Computational
namespace BitCounterMachine
open Turing.TM2 NatPrefixMachine.Stack

/-- Bit-level predecessor; its canonical-input law is proved below. -/
def predBits : List Bool → List Bool
  | [] => []
  | true::[] => []
  | true::b::bs => false::b::bs
  | false::bs => true::predBits bs

theorem predBits_bits (n : Nat) : predBits n.bits = (n-1).bits := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hb ih =>
    rw [Nat.bits_append_bit n b hb]
    cases b with
    | false =>
      have hn : n ≠ 0 := by intro h; exact Bool.false_ne_true (hb h)
      have he : Nat.bit false n - 1 = 2*(n-1)+1 := by change 2*n-1 = 2*(n-1)+1; omega
      simp only [predBits,ih,he,Nat.bit1_bits]
    | true =>
      by_cases hn : n = 0
      · subst n; rfl
      · have hbits : n.bits ≠ [] := by
          intro he
          have hs : n.size = 0 := by rw [←Nat.size_eq_bits_len,he]; rfl
          exact hn (Nat.size_eq_zero.mp hs)
        have he : Nat.bit true n - 1 = 2*n := by simp [Nat.bit]
        rw [he,Nat.bit0_bits n hn]
        cases hx : n.bits with
        | nil => exact (hbits hx).elim
        | cons a xs => rfl

abbrev Config := Cfg (fun _ : NatPrefixMachine.Stack => Bool) Bool (Option Bool)

def program : Bool → Stmt (fun _ : NatPrefixMachine.Stack => Bool) Bool (Option Bool)
  | false => .pop output (fun _ b => b) <|
      .branch Option.isSome
        (.branch (fun b => b.getD false)
          (.peek output (fun _ b => b) <| .branch Option.isSome
            (.push output (fun _ => false) (.goto (fun _ => true))) (.goto (fun _ => true)))
          (.push scratch (fun _ => true) (.goto (fun _ => false))))
        (.load (fun _ => some false) .halt)
  | true => .pop scratch (fun _ b => b) <|
      .branch Option.isSome
        (.push output (fun b => b.getD false) (.goto (fun _ => true)))
        (.load (fun _ => some true) .halt)

def config (phase : Option Bool) (counter temp source frame : List Bool)
    (v : Option Bool := none) : Config :=
  ⟨phase,v,fun k => match k with
    | output => counter | scratch => temp | input => source | count => frame⟩

def tick (c : Config) : Config := (step program c).getD c

theorem supports : Supports program Finset.univ := by
  constructor
  · simp
  · intro q _
    cases q <;> simp [program,SupportsStmt]

private theorem borrow_zero (temp source frame : List Bool) (v : Option Bool) :
    tick (config (some false) [] temp source frame v) =
      config none [] temp source frame (some false) := by
  simp [tick,config,program,stepAux,Function.update]

private theorem borrow_false (bs temp source frame : List Bool) (v : Option Bool) :
    tick (config (some false) (false::bs) temp source frame v) =
      config (some false) bs (true::temp) source frame (some false) := by
  simp [tick,config,program,stepAux]
  funext k
  cases k <;> simp

private theorem borrow_true (bs temp source frame : List Bool) (v : Option Bool) :
    tick (config (some false) (true::bs) temp source frame v) =
      config (some true) (if bs = [] then [] else false::bs) temp source frame bs.head? := by
  cases bs with
  | nil =>
    simp [tick,config,program,stepAux]
    funext k
    cases k <;> simp
  | cons b bs =>
    simp [tick,config,program,stepAux]
    funext k
    cases k <;> simp

private theorem restore_step (counter temp source frame : List Bool) (v : Option Bool) :
    tick (config (some true) counter temp source frame v) = match temp with
      | [] => config none counter [] source frame (some true)
      | b::bs => config (some true) (b::counter) bs source frame (some b) := by
  cases temp with
  | nil => simp [tick,config,program,stepAux,Function.update]
  | cons b bs =>
    simp [tick,config,program,stepAux]
    funext k
    cases k <;> simp

private theorem markers_cons (k : Nat) (temp : List Bool) :
    List.replicate k true ++ true::temp = true::(List.replicate k true ++ temp) := by
  calc
    _ = (List.replicate k true ++ [true]) ++ temp := by simp
    _ = List.replicate (k+1) true ++ temp := by rw [←List.replicate_succ']
    _ = _ := by rw [List.replicate_succ,List.cons_append]

private theorem borrow_run (k : Nat) (bs temp source frame : List Bool) (v : Option Bool) :
    tick^[k+1] (config (some false) (List.replicate k false ++ true::bs) temp source frame v) =
      config (some true) (if bs = [] then [] else false::bs)
        (List.replicate k true ++ temp) source frame bs.head? := by
  induction k generalizing temp v with
  | zero => simp [borrow_true]
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    simp only [List.replicate_succ,List.cons_append,borrow_false]
    rw [ih,markers_cons]

private theorem restore_run (counter temp source frame : List Bool) (v : Option Bool) :
    tick^[temp.length+1] (config (some true) counter temp source frame v) =
      config none (temp.reverse++counter) [] source frame (some true) := by
  induction temp generalizing counter v with
  | nil => simp [restore_step]
  | cons b bs ih =>
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,restore_step,ih]
    simp

theorem borrow_chain_run (k : Nat) (bs source frame : List Bool) (v : Option Bool) :
    tick^[2*k+2] (config (some false) (List.replicate k false ++ true::bs) [] source frame v) =
      config none (List.replicate k true ++ if bs = [] then [] else false::bs)
        [] source frame (some true) := by
  have hn : 2*k+2 = (k+1)+(k+1) := by omega
  rw [hn,Function.iterate_add_apply tick (k+1) (k+1),borrow_run]
  simp only [List.append_nil]
  simpa using restore_run (if bs = [] then [] else false::bs) (List.replicate k true) source frame bs.head?

private theorem predBits_chain (k : Nat) (bs : List Bool) :
    predBits (List.replicate k false ++ true::bs) =
      List.replicate k true ++ if bs = [] then [] else false::bs := by
  induction k with
  | zero => cases bs <;> rfl
  | succ k ih => simpa only [List.replicate_succ,List.cons_append,predBits] using congrArg (List.cons true) ih

private theorem word_cases (word : List Bool) :
    (∃ k, word = List.replicate k false) ∨
      ∃ k bs, word = List.replicate k false ++ true::bs := by
  induction word with
  | nil => exact Or.inl ⟨0,rfl⟩
  | cons b word ih =>
    cases b with
    | true => exact Or.inr ⟨0,word,rfl⟩
    | false =>
      rcases ih with ⟨k,rfl⟩ | ⟨k,bs,rfl⟩
      · exact Or.inl ⟨k+1,rfl⟩
      · exact Or.inr ⟨k+1,bs,rfl⟩

/-- Every canonical counter has a complete bounded run. The two other stacks
and the canonical representation are retained; zero reports underflow. -/
theorem run (n : Nat) (source frame : List Bool) (v : Option Bool) :
    ∃ fuel ≤ 2*n.size+1,
      tick^[fuel] (config (some false) n.bits [] source frame v) =
        config none (n-1).bits [] source frame (some (decide (n ≠ 0))) := by
  by_cases hn : n = 0
  · subst n
    exact ⟨1,by decide,borrow_zero [] source frame v⟩
  · rcases word_cases n.bits with ⟨k,hk⟩ | ⟨k,bs,hk⟩
    · cases k with
      | zero =>
        have hs : n.size = 0 := by rw [←Nat.size_eq_bits_len,hk]; rfl
        exact (hn (Nat.size_eq_zero.mp hs)).elim
      | succ k =>
        have hc := natPayload_canonical n
        rw [hk] at hc
        exact (hc (by rw [List.reverse_replicate,List.replicate_succ]; rfl)).elim
    · have hlen := congrArg List.length hk
      simp only [List.length_append,List.length_replicate,List.length_cons,Nat.size_eq_bits_len] at hlen
      refine ⟨2*k+2,by omega,?_⟩
      have hp := predBits_bits n
      rw [hk,predBits_chain] at hp
      rw [hk,borrow_chain_run,hp]
      simp [hn]

/-- The data interface after the actual prefix-parser run establishes the
counter invariant. Only the control label changes; all stacks are retained.
This relates two concrete runs, not a compiled sequential program or its cost. -/
theorem parsed_run (word : List Bool) (n : Nat) (suffix : List Bool)
    (h : uniformNatRead word = some (n,suffix)) :
    ∃ fuel ≤ 2*n.size+1,
      let parsed := NatPrefixMachine.tick^[3*n.size+3] (NatPrefixMachine.start word)
      tick^[fuel] ⟨some false,parsed.var,parsed.stk⟩ =
        config none (n-1).bits [] suffix [] (some (decide (n ≠ 0))) := by
  rw [NatPrefixMachine.accepted_run word n suffix h]
  have he : (⟨some false,(NatPrefixMachine.config none suffix [] [] n.bits (some true)).var,
      (NatPrefixMachine.config none suffix [] [] n.bits (some true)).stk⟩ : Config) =
      config (some false) n.bits [] suffix [] (some true) := by
    congr 1
    funext k
    cases k <;> rfl
  dsimp only
  rw [he]
  exact run n suffix [] (some true)

theorem borrow_control :
    tick^[8] (config (some false) [false,false,false,true] [] [true,false] [false]) =
      config none [true,true,true] [] [true,false] [false] (some true) := by
  exact borrow_chain_run 3 [] [true,false] [false] none

theorem one_control :
    tick^[2] (config (some false) [true] [] [false,true] [true]) =
      config none [] [] [false,true] [true] (some true) := by
  exact borrow_chain_run 0 [] [false,true] [true] none

/-- Higher bits retain a low zero when decrementing an odd counter above one. -/
theorem odd_control :
    tick^[2] (config (some false) [true,true] [] [false,true] [true]) =
      config none [false,true] [] [false,true] [true] (some true) := by
  exact borrow_chain_run 0 [true] [false,true] [true] none

theorem zero_control :
    tick (config (some false) [] [] [true] [false]) =
      config none [] [] [true] [false] (some false) := borrow_zero [] [true] [false] none

theorem underflow_distinct :
    (tick (config (some false) [] [] [] [])).var ≠
      (tick^[2] (config (some false) [true] [] [] [])).var := by decide

theorem borrow_not_erased :
    (tick^[8] (config (some false) [false,false,false,true] [] [] [])).stk output ≠
      [false,false,false] := by decide

#print axioms predBits_bits
#print axioms supports
#print axioms borrow_chain_run
#print axioms run
#print axioms parsed_run
#print axioms borrow_control
#print axioms one_control
#print axioms odd_control
#print axioms zero_control
#print axioms underflow_distinct
#print axioms borrow_not_erased
end BitCounterMachine
end ExplainableCrypto.Helios.Computational
