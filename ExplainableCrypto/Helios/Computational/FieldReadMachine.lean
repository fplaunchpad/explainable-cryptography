import ExplainableCrypto.Helios.Computational.BitCounterMachine
import ExplainableCrypto.Helios.Computational.TM2ReturnLink

/-! Length-controlled field reading with an executed binary-decrement subroutine.
A short input is rejected before another decrement; no unary count is allocated. -/
namespace ExplainableCrypto.Helios.Computational.FieldReadMachine
open Turing.TM2 NatPrefixMachine.Stack

inductive Label where
  | scan | counter (phase : Bool) | restore
  deriving DecidableEq
open Label
instance : Inhabited Label := ⟨scan⟩
instance : Fintype Label where
  elems := {scan,counter false,counter true,restore}
  complete l := by cases l with
    | scan => simp
    | restore => simp
    | counter b => cases b <;> simp

abbrev Config := Cfg (fun _ : NatPrefixMachine.Stack => Bool) Label (Option Bool)
def config (phase : Option Label) (counter temp source collected : List Bool)
    (v : Option Bool := none) : Config :=
  ⟨phase,v,fun k => match k with
    | output => counter | scratch => temp | input => source | count => collected⟩

def program : Label → Stmt (fun _ : NatPrefixMachine.Stack => Bool) Label (Option Bool)
  | scan => .peek output (fun _ b => b) <| .branch Option.isSome
      (.pop input (fun _ b => b) <| .branch Option.isSome
        (.push count (fun b => b.getD false) (.goto (fun _ => counter false)))
        (.load (fun _ => some false) .halt))
      (.goto (fun _ => restore))
  | counter b => TM2ReturnLink.redirect counter scan (BitCounterMachine.program b)
  | restore => .pop count (fun _ b => b) <| .branch Option.isSome
      (.push output (fun b => b.getD false) (.goto (fun _ => restore)))
      (.load (fun _ => some true) .halt)

def tick (c : Config) : Config := (step program c).getD c

theorem supports : Supports program Finset.univ := by
  constructor
  · simp
  · intro l _
    cases l with
    | scan => simp [program,SupportsStmt]
    | restore => simp [program,SupportsStmt]
    | counter b => cases b <;>
        simp [program,TM2ReturnLink.redirect,BitCounterMachine.program,SupportsStmt]

/-- The decrement subroutine really returns to this reader's control label. -/
theorem counter_run (n : Nat) (source collected : List Bool) (v : Option Bool) :
    ∃ fuel ≤ 2*n.size+1,
      tick^[fuel] (config (some (counter false)) n.bits [] source collected v) =
        config (some scan) (n-1).bits [] source collected (some (decide (n ≠ 0))) := by
  obtain ⟨fuel,hf,he⟩ := BitCounterMachine.run n source collected v
  have hh : ((TM2ReturnLink.tick BitCounterMachine.program)^[fuel]
      (BitCounterMachine.config (some false) n.bits [] source collected v)).l = none := by
    change (BitCounterMachine.tick^[fuel] _).l = none
    rw [he]; rfl
  obtain ⟨used,hu,hr⟩ := TM2ReturnLink.run BitCounterMachine.program program counter scan
    (fun _ => rfl) fuel (BitCounterMachine.config (some false) n.bits [] source collected v) hh
  refine ⟨used,hu.trans hf,?_⟩
  change tick^[used] _ = TM2ReturnLink.embed counter scan (BitCounterMachine.tick^[fuel] _) at hr
  rw [he] at hr
  exact hr

private theorem read_zero (source collected : List Bool) (v : Option Bool) :
    tick (config (some scan) [] [] source collected v) =
      config (some restore) [] [] source collected none := by
  simp [tick,config,program,stepAux]

private theorem read_missing (b : Bool) (bs collected : List Bool) (v : Option Bool) :
    tick (config (some scan) (b::bs) [] [] collected v) =
      config none (b::bs) [] [] collected (some false) := by
  simp [tick,config,program,stepAux,Function.update]

private theorem read_bit (b a : Bool) (bs source collected : List Bool) (v : Option Bool) :
    tick (config (some scan) (a::bs) [] (b::source) collected v) =
      config (some (counter false)) (a::bs) [] source (b::collected) (some b) := by
  simp [tick,config,program,stepAux]
  funext k
  cases k <;> simp

private theorem bits_nonempty {n : Nat} (h : n ≠ 0) : n.bits ≠ [] := by
  intro he
  have hs : n.size = 0 := by rw [←Nat.size_eq_bits_len,he]; rfl
  exact h (Nat.size_eq_zero.mp hs)

private theorem read_positive (n : Nat) (h : n ≠ 0) (b : Bool)
    (source collected : List Bool) (v : Option Bool) :
    tick (config (some scan) n.bits [] (b::source) collected v) =
      config (some (counter false)) n.bits [] source (b::collected) (some b) := by
  cases hb : n.bits with
  | nil => exact (bits_nonempty h hb).elim
  | cons a bs => exact read_bit b a bs source collected v

private theorem restore_run (counter source collected : List Bool) (v : Option Bool) :
    tick^[collected.length+1] (config (some restore) counter [] source collected v) =
      config none (collected.reverse++counter) [] source [] (some true) := by
  induction collected generalizing counter v with
  | nil => simp [tick,config,program,stepAux,Function.update]
  | cons b bs ih =>
    have hs : tick (config (some restore) counter [] source (b::bs) v) =
        config (some restore) (b::counter) [] source bs (some b) := by
      simp [tick,config,program,stepAux]
      funext k
      cases k <;> simp
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,hs,ih]
    simp

/-- Consume a known prefix, retaining the remaining binary count and all data.
The prefix is collected in reverse before the separate final restore phase. -/
theorem consume_run (bs suffix collected : List Bool) (n : Nat) (v : Option Bool) :
    ∃ fuel ≤ bs.length*(2*(n+bs.length).size+2), ∃ mem,
      tick^[fuel] (config (some scan) (n+bs.length).bits [] (bs++suffix) collected v) =
        config (some scan) n.bits [] suffix (bs.reverse++collected) mem := by
  induction bs generalizing collected v with
  | nil => exact ⟨0,by simp,v,by simp⟩
  | cons b bs ih =>
    obtain ⟨k,hk,hd⟩ := counter_run (n+(b::bs).length) (bs++suffix) (b::collected) (some b)
    have hn : n+(b::bs).length ≠ 0 := by simp
    have he : n+(b::bs).length-1 = n+bs.length := by simp
    have hd' : tick^[k+1] (config (some scan) (n+(b::bs).length).bits []
        ((b::bs)++suffix) collected v) =
        config (some scan) (n+bs.length).bits [] (bs++suffix) (b::collected) (some true) := by
      rw [Function.iterate_succ_apply,List.cons_append,read_positive _ hn,hd,he]
      simp only [hn,ne_eq,not_false_eq_true,decide_true]
    obtain ⟨j,hj,mem,hr⟩ := ih (b::collected) (some true)
    refine ⟨j+(k+1),?_,mem,?_⟩
    · have hs := Nat.size_le_size (show n+bs.length ≤ n+(b::bs).length by simp)
      have hm := Nat.mul_le_mul_left bs.length (show 2*(n+bs.length).size+2 ≤
          2*(n+(b::bs).length).size+2 by omega)
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hk hm ⊢
      omega
    · rw [Function.iterate_add_apply,hd',hr]
      simp

/-- Read exactly one field and retain its suffix, including empty fields. -/
theorem run (bs suffix : List Bool) (v : Option Bool) :
    ∃ fuel ≤ bs.length*(2*bs.length.size+3)+2,
      tick^[fuel] (config (some scan) bs.length.bits [] (bs++suffix) [] v) =
        config none bs [] suffix [] (some true) := by
  obtain ⟨k,hk,mem,he⟩ := consume_run bs suffix [] 0 v
  simp only [Nat.zero_add,List.append_nil] at hk he
  have hs : tick^[bs.length+2] (config (some scan) [] [] suffix bs.reverse mem) =
      config none bs [] suffix [] (some true) := by
    rw [Function.iterate_succ_apply,read_zero]
    simpa using restore_run [] suffix bs.reverse none
  refine ⟨(bs.length+2)+k,?_,?_⟩
  · simp only [Nat.mul_succ] at hk ⊢
    omega
  · rw [Function.iterate_add_apply,he]
    exact hs

/-- Reject short input after consuming only the available bits. The bound
uses declared bit width, never an expansion of the declared numeric length. -/
theorem truncated_run (n : Nat) (bs : List Bool) (h : bs.length < n) (v : Option Bool) :
    ∃ fuel ≤ bs.length*(2*n.size+2)+1,
      tick^[fuel] (config (some scan) n.bits [] bs [] v) =
        config none (n-bs.length).bits [] [] bs.reverse (some false) := by
  obtain ⟨k,hk,mem,he⟩ := consume_run bs [] [] (n-bs.length) v
  have hn : n-bs.length+bs.length = n := by omega
  simp only [hn,List.append_nil] at hk he
  have hs : tick (config (some scan) (n-bs.length).bits [] [] bs.reverse mem) =
      config none (n-bs.length).bits [] [] bs.reverse (some false) := by
    cases hb : (n-bs.length).bits with
    | nil => exact (bits_nonempty (by omega) hb).elim
    | cons b rest => exact read_missing b rest bs.reverse mem
  exact ⟨k+1,by omega,by rw [Function.iterate_succ_apply',he,hs]⟩

/-- Semantic readout after halt; rejected partial fields are not returned. -/
def readout (c : Config) : Option (List Bool × List Bool) :=
  if c.l = none ∧ c.var = some true then some (c.stk output,c.stk input) else none

/-- All inputs halt. The cost depends on available input and binary width,
including adversarially huge declared lengths and zero-length fields. -/
theorem total_run (n : Nat) (word : List Bool) (v : Option Bool) :
    ∃ fuel ≤ (min n word.length+1)*(2*n.size+4),
      let c := tick^[fuel] (config (some scan) n.bits [] word [] v)
      c.l = none ∧ readout c =
        if n ≤ word.length then some (word.take n,word.drop n) else none := by
  by_cases h : n ≤ word.length
  · obtain ⟨k,hk,he⟩ := run (word.take n) (word.drop n) v
    have hl := List.length_take_of_le h
    rw [hl,List.take_append_drop] at he
    rw [hl] at hk
    refine ⟨k,?_,?_⟩
    · rw [Nat.min_eq_left h,Nat.add_mul,Nat.one_mul,Nat.mul_add] at ⊢
      simp only [Nat.mul_add] at hk
      omega
    · rw [he,if_pos h]
      simp [readout,config]
  · obtain ⟨k,hk,he⟩ := truncated_run n word (by omega) v
    refine ⟨k,?_,?_⟩
    · rw [Nat.min_eq_right (by omega),Nat.add_mul,Nat.one_mul,Nat.mul_add]
      simp only [Nat.mul_add] at hk
      omega
    · rw [he,if_neg h]
      simp [readout,config]

theorem suffix_control :
    tick^[12] (config (some scan) [false,true] [] [false,true,true,false] []) =
      config none [false,true] [] [true,false] [] (some true) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  cases k <;> rfl

theorem zero_control :
    tick^[2] (config (some scan) [] [] [true,false] []) =
      config none [] [] [true,false] [] (some true) := by
  simp [tick,config,program,stepAux,Function.update]

theorem huge_empty_control :
    tick (config (some scan) (List.replicate 256 false ++ [true]) [] [] []) =
      config none (List.replicate 256 false ++ [true]) [] [] [] (some false) := by
  exact read_missing false (List.replicate 255 false ++ [true]) [] none

theorem no_padding_control :
    tick^[6] (config (some scan) [false,true] [] [true] []) =
      config none [true] [] [] [true] (some false) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  cases k <;> rfl

theorem no_reversal_control :
    (tick^[12] (config (some scan) [false,true] [] [false,true,true,false] [])).stk output ≠
      [true,false] := by decide

#print axioms supports
#print axioms counter_run
#print axioms consume_run
#print axioms run
#print axioms truncated_run
#print axioms total_run
#print axioms suffix_control
#print axioms zero_control
#print axioms huge_empty_control
#print axioms no_padding_control
#print axioms no_reversal_control
end ExplainableCrypto.Helios.Computational.FieldReadMachine
