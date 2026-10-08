import ExplainableCrypto.Helios.Computational.FieldReadMachine

/-! A single TM2 program parses the existing length header and reads its field. -/
namespace ExplainableCrypto.Helios.Computational.FieldPrefixMachine
open Turing.TM2 NatPrefixMachine.Stack
inductive Label where
  | header (phase : NatPrefixMachine.Label)
  | field (phase : FieldReadMachine.Label)
  | enter | finish
  deriving DecidableEq
open Label
instance : Inhabited Label := ⟨header .width⟩
instance : Fintype Label where
  elems := (Finset.univ.image header) ∪ (Finset.univ.image field) ∪ {enter,finish}
  complete l := by cases l <;> simp

abbrev Config := Cfg (fun _ : NatPrefixMachine.Stack => Bool) Label (Option Bool)
def program : Label → Stmt (fun _ : NatPrefixMachine.Stack => Bool) Label (Option Bool)
  | header p => TM2ReturnLink.redirect header enter (NatPrefixMachine.program p)
  | field p => TM2ReturnLink.redirect field finish (FieldReadMachine.program p)
  | enter => .branch (fun v => decide (v = some true))
      (.goto (fun _ => field .scan)) .halt
  | finish => .halt

def tick (c : Config) : Config := (step program c).getD c

def start (word : List Bool) : Config :=
  TM2ReturnLink.embed header enter (NatPrefixMachine.start word)

def readout (c : Config) : Option (List Bool × List Bool) :=
  if c.l = none ∧ c.var = some true then some (c.stk output,c.stk input) else none

/-- Original field semantics, including rejection of short payloads. -/
def decode (word : List Bool) : Option (List Bool × List Bool) := do
  let (n,rest) ← uniformNatRead word
  if n ≤ rest.length then some (rest.take n,rest.drop n) else none

private theorem redirect_supports {L : Type*} (f : L → Label) (ret : Label)
    (s : Stmt (fun _ : NatPrefixMachine.Stack => Bool) L (Option Bool)) :
    SupportsStmt Finset.univ (TM2ReturnLink.redirect f ret s) := by
  induction s <;> simp_all [TM2ReturnLink.redirect,SupportsStmt]

theorem supports : Supports program Finset.univ := by
  constructor
  · simp
  · intro l _
    cases l <;> simp [program,redirect_supports,SupportsStmt]

private theorem field_finish (c : FieldReadMachine.Config) (h : c.l = none) :
    tick (TM2ReturnLink.embed field finish c) = ⟨none,c.var,c.stk⟩ := by
  cases c with
  | mk l v tapes => change l = none at h; subst l; rfl

private theorem prefix_enter (n : Nat) (rest : List Bool) :
    tick (TM2ReturnLink.embed header enter
      (NatPrefixMachine.config none rest [] [] n.bits (some true))) =
      TM2ReturnLink.embed field finish
        (FieldReadMachine.config (some .scan) n.bits [] rest [] (some true)) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  cases k <;> rfl

/-- A successful original header parse executes in this program and enters
field control; the canonical counter and all remaining input are derived. -/
theorem prefix_run (word : List Bool) (n : Nat) (rest : List Bool)
    (h : uniformNatRead word = some (n,rest)) :
    ∃ fuel ≤ 3*n.size+4,
      tick^[fuel] (start word) = TM2ReturnLink.embed field finish
        (FieldReadMachine.config (some .scan) n.bits [] rest [] (some true)) := by
  have he := NatPrefixMachine.accepted_run word n rest h
  have hh : ((TM2ReturnLink.tick NatPrefixMachine.program)^[3*n.size+3]
      (NatPrefixMachine.start word)).l = none := by
    change (NatPrefixMachine.tick^[3*n.size+3] _).l = none
    rw [he]; rfl
  obtain ⟨k,hk,hr⟩ := TM2ReturnLink.run NatPrefixMachine.program program header enter
    (fun _ => rfl) _ (NatPrefixMachine.start word) hh
  change tick^[k] (start word) = TM2ReturnLink.embed header enter
    (NatPrefixMachine.tick^[3*n.size+3] _) at hr
  rw [he] at hr
  exact ⟨k+1,by omega,by rw [Function.iterate_succ_apply',hr,prefix_enter]⟩

/-- After an accepted length header, one linked program returns the exact field
or rejection. Both control transfers and the final halt are charged. -/
theorem accepted_run (word : List Bool) (n : Nat) (rest : List Bool)
    (h : uniformNatRead word = some (n,rest)) :
    ∃ fuel ≤ 3*n.size+5+(min n rest.length+1)*(2*n.size+4),
      let c := tick^[fuel] (start word)
      c.l = none ∧ readout c = decode word := by
  obtain ⟨k,hk,hp⟩ := prefix_run word n rest h
  obtain ⟨j,hj,hhalt,hout⟩ := FieldReadMachine.total_run n rest (some true)
  let c := FieldReadMachine.tick^[j]
    (FieldReadMachine.config (some .scan) n.bits [] rest [] (some true))
  obtain ⟨u,hu,hr⟩ := TM2ReturnLink.run FieldReadMachine.program program field finish
    (fun _ => rfl) j (FieldReadMachine.config (some .scan) n.bits [] rest [] (some true)) hhalt
  change tick^[u] _ = TM2ReturnLink.embed field finish c at hr
  have he : tick^[1+(u+k)] (start word) = ⟨none,c.var,c.stk⟩ := by
    rw [Function.iterate_add_apply tick 1,Function.iterate_add_apply tick u k,hp,hr]
    exact field_finish c hhalt
  refine ⟨1+(u+k),by omega,?_⟩
  rw [he]
  refine ⟨rfl,?_⟩
  have ho : readout ⟨none,c.var,c.stk⟩ = FieldReadMachine.readout c := by
    simp [readout,FieldReadMachine.readout,c,hhalt]
  rw [ho,hout]
  simp [decode,h]

/-- Failed natural prefixes halt as rejection; they never enter field control. -/
theorem rejected_prefix (word : List Bool) (h : uniformNatRead word = none) :
    ∃ fuel ≤ 3*word.length+4,
      let c := tick^[fuel] (start word)
      c.l = none ∧ readout c = none := by
  obtain ⟨j,hj,hhalt,hout⟩ := NatPrefixMachine.total_run word
  let c := NatPrefixMachine.tick^[j] (NatPrefixMachine.start word)
  change c.l = none at hhalt
  change NatPrefixMachine.readout c = (uniformNatRead word).map (fun p => (p.1.bits,p.2)) at hout
  have hv : c.var ≠ some true := by
    intro hv
    simp only [h,Option.map_none,NatPrefixMachine.readout,hhalt,hv,and_self,ite_true] at hout
    contradiction
  obtain ⟨k,hk,hr⟩ := TM2ReturnLink.run NatPrefixMachine.program program header enter
    (fun _ => rfl) j (NatPrefixMachine.start word) hhalt
  change tick^[k] (start word) = TM2ReturnLink.embed header enter c at hr
  have hs : tick (TM2ReturnLink.embed header enter c) = ⟨none,c.var,c.stk⟩ := by
    simp [tick,TM2ReturnLink.embed,hhalt,program,stepAux,hv]
  refine ⟨k+1,by omega,?_⟩
  rw [Function.iterate_succ_apply',hr,hs]
  simp [readout,hv]

/-- Every raw input halts with exact field-decoder agreement and a polynomial
bound in input length. No successful parsing premise or numeric-length bound. -/
theorem total_run (word : List Bool) :
    ∃ fuel ≤ 3*word.length+5+(word.length+1)*(2*word.length+4),
      let c := tick^[fuel] (start word)
      c.l = none ∧ readout c = decode word := by
  cases h : uniformNatRead word with
  | none =>
    obtain ⟨k,hk,he⟩ := rejected_prefix word h
    exact ⟨k,by omega,he.1,by simpa [decode,h] using he.2⟩
  | some pair =>
    rcases pair with ⟨n,rest⟩
    obtain ⟨k,hk,he⟩ := accepted_run word n rest h
    have hw := uniformNatRead_exact word n rest h
    have hl : 2*n.size+1+rest.length = word.length := by
      rw [hw,List.length_append,uniformNatEncode_length]
    have hs : n.size ≤ word.length := by omega
    have hm := Nat.mul_le_mul
      (show min n rest.length+1 ≤ word.length+1 by have := Nat.min_le_right n rest.length; omega)
      (show 2*n.size+4 ≤ 2*word.length+4 by omega)
    exact ⟨k,by omega,he⟩

/-- The existing record decoder supplies the actual field framing. Only the
already established outer count header is dropped; the original codec is unchanged. -/
theorem singleton_record_run (word bs : List Bool)
    (h : bitFieldsDecode word = some [bs]) :
    ∃ fuel ≤ 3*(word.drop 3).length+5+
        ((word.drop 3).length+1)*(2*(word.drop 3).length+4),
      let c := tick^[fuel] (start (word.drop 3))
      c.l = none ∧ readout c = some (bs,[]) := by
  obtain ⟨k,hk,he⟩ := total_run (word.drop 3)
  refine ⟨k,hk,he.1,?_⟩
  rw [he.2,bitFieldsDecode_exact word [bs] h]
  have hw : (bitFieldsEncode [bs]).drop 3 = uniformNatEncode bs.length ++ bs := by
    change (uniformNatEncode 1 ++ (uniformNatEncode bs.length ++ bs ++ [])).drop 3 = _
    rw [show uniformNatEncode 1 = [true,false,true] by decide]
    simp
  rw [hw]
  simp [decode,uniformNatRead_encode]

theorem field_control :
    readout (tick^[24] (start [true,true,false,false,true,false,true,true,false])) =
      some ([false,true],[true,false]) := by decide

theorem empty_control :
    readout (tick^[7] (start [false,true,false])) = some ([],[true,false]) := by decide

theorem rejection_controls :
    (tick^[6] (start [true,false,false])).l = none ∧
    readout (tick^[6] (start [true,false,false])) = none ∧
    (tick^[20] (start [true,true,false,false,true,true])).l = none ∧
    readout (tick^[20] (start [true,true,false,false,true,true])) = none := by decide

#print axioms singleton_record_run
#print axioms field_control
#print axioms empty_control
#print axioms rejection_controls
#print axioms supports
#print axioms prefix_run
#print axioms accepted_run
#print axioms rejected_prefix
#print axioms total_run
end ExplainableCrypto.Helios.Computational.FieldPrefixMachine
