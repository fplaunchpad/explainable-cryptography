import ExplainableCrypto.Helios.Computational.BitCounterMachine

/-! Canonical binary increment needed to construct original cache record lengths.
All carries and restoration execute on the existing four binary stacks. -/
namespace ExplainableCrypto.Helios.Computational.BitIncrementMachine
open Turing.TM2 NatPrefixMachine.Stack

def succBits : List Bool → List Bool
  | [] => [true]
  | false::bs => true::bs
  | true::bs => false::succBits bs

theorem succBits_bits (n : Nat) : succBits n.bits = (n+1).bits := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b with
    | false =>
      change true::n.bits = (2*n+1).bits
      rw [Nat.bit1_bits]
    | true =>
      change false::succBits n.bits = (2*n+1+1).bits
      rw [ih,show 2*n+1+1 = 2*(n+1) by omega,Nat.bit0_bits (n+1) (by omega)]

abbrev Config := Cfg (fun _ : NatPrefixMachine.Stack => Bool) Bool (Option Bool)

def program : Bool → Stmt (fun _ : NatPrefixMachine.Stack => Bool) Bool (Option Bool)
  | false => .pop output (fun _ b => b) <| .branch (fun b => b.getD false)
      (.push scratch (fun _ => false) (.goto (fun _ => false)))
      (.push output (fun _ => true) (.goto (fun _ => true)))
  | true => .pop scratch (fun _ b => b) <| .branch Option.isSome
      (.push output (fun b => b.getD false) (.goto (fun _ => true)))
      (.load (fun _ => some true) .halt)

def tick (c : Config) : Config := (step program c).getD c
abbrev config (phase : Option Bool) (word temp source frame : List Bool) (v : Option Bool) : Config :=
  BitCounterMachine.config phase word temp source frame v

theorem supports : Supports program Finset.univ := by
  constructor
  · simp
  · intro l _
    cases l <;> simp [program,SupportsStmt]

private theorem restore_run (word temp source frame : List Bool) (v : Option Bool) :
    tick^[temp.length+1] (config (some true) word temp source frame v) =
      config none (temp.reverse++word) [] source frame (some true) := by
  induction temp generalizing word v with
  | nil => simp [tick,config,BitCounterMachine.config,program,stepAux]
  | cons b bs ih =>
    have hs : tick (config (some true) word (b::bs) source frame v) =
        config (some true) (b::word) bs source frame (some b) := by
      simp [tick,config,BitCounterMachine.config,program,stepAux]
      funext k
      cases k <;> simp
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,hs,ih]
    simp

private theorem carry_run (word temp source frame : List Bool) (v : Option Bool) :
    ∃ fuel ≤ 2*word.length+temp.length+2,
      tick^[fuel] (config (some false) word temp source frame v) =
        config none (temp.reverse++succBits word) [] source frame (some true) := by
  induction word generalizing temp v with
  | nil =>
    have hs : tick (config (some false) [] temp source frame v) =
        config (some true) [true] temp source frame none := by
      simp [tick,config,BitCounterMachine.config,program,stepAux]
      funext k
      cases k <;> simp
    refine ⟨temp.length+1+1,by simp,?_⟩
    rw [Function.iterate_succ_apply,hs,restore_run]
    rfl
  | cons b bs ih =>
    cases b with
    | false =>
      have hs : tick (config (some false) (false::bs) temp source frame v) =
          config (some true) (true::bs) temp source frame (some false) := by
        simp [tick,config,BitCounterMachine.config,program,stepAux]
        funext k
        cases k <;> simp
      refine ⟨temp.length+1+1,by simp,?_⟩
      rw [Function.iterate_succ_apply,hs,restore_run]
      rfl
    | true =>
      have hs : tick (config (some false) (true::bs) temp source frame v) =
          config (some false) bs (false::temp) source frame (some true) := by
        simp [tick,config,BitCounterMachine.config,program,stepAux]
        funext k
        cases k <;> simp
      obtain ⟨j,hj,hr⟩ := ih (false::temp) (some true)
      refine ⟨j+1,by simp only [List.length_cons] at *; omega,?_⟩
      rw [Function.iterate_succ_apply,hs,hr]
      simp [succBits]

/-- Complete canonical increment, preserving both other stacks and clearing the
carry workspace. Neither numeric conversion nor a carry is a host callback. -/
theorem run (n : Nat) (source frame : List Bool) (v : Option Bool) :
    ∃ fuel ≤ 2*n.size+2,
      tick^[fuel] (config (some false) n.bits [] source frame v) =
        config none (n+1).bits [] source frame (some true) := by
  obtain ⟨j,hj,hr⟩ := carry_run n.bits [] source frame v
  refine ⟨j,?_,?_⟩
  · simpa only [List.length_nil,Nat.add_zero,Nat.size_eq_bits_len] using hj
  · simpa only [List.reverse_nil,List.nil_append,succBits_bits] using hr

theorem carry_control :
    ∃ fuel ≤ 8,
      tick^[fuel] (config (some false) [true,true,true] [] [false,true] [true,false] none) =
        config none [false,false,false,true] [] [false,true] [true,false] (some true) := by
  exact run 7 [false,true] [true,false] none

theorem low_zero_control :
    ∃ fuel ≤ 6,
      tick^[fuel] (config (some false) [false,true] [] [true] [false] none) =
        config none [true,true] [] [true] [false] (some true) := by
  exact run 2 [true] [false] none

theorem zero_control :
    ∃ fuel ≤ 2,
      tick^[fuel] (config (some false) [] [] [true,false] [] none) =
        config none [true] [] [true,false] [] (some true) := by
  exact run 0 [true,false] [] none

#print axioms succBits_bits
#print axioms supports
#print axioms run
#print axioms carry_control
#print axioms low_zero_control
#print axioms zero_control
end ExplainableCrypto.Helios.Computational.BitIncrementMachine
