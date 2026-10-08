import ExplainableCrypto.Helios.Computational.FieldPrefixMachine
import ExplainableCrypto.Helios.Computational.TM2StackFrame

/-! One record-field iteration on six binary stacks. The field reader preserves
outer count/archive; decrement then updates that count and preserves the field. -/
namespace ExplainableCrypto.Helios.Computational.RecordFieldStepMachine
open Turing.TM2 NatPrefixMachine.Stack
abbrev Stack := NatPrefixMachine.Stack ⊕ Bool

def fieldLayout : NatPrefixMachine.Stack ⊕ Bool ≃ Stack := Equiv.refl _
def counterLayout : NatPrefixMachine.Stack ⊕ Bool ≃ Stack :=
  Equiv.swap (.inl output) (.inr false)
def frame (outer archive : List Bool) : Bool → List Bool := fun b => if b then archive else outer

def fieldProgram (l : FieldPrefixMachine.Label) :=
  TM2StackFrame.relocate fieldLayout (FieldPrefixMachine.program l)
def counterProgram (b : Bool) :=
  TM2StackFrame.relocate counterLayout (BitCounterMachine.program b)

inductive Label where
  | field (phase : FieldPrefixMachine.Label) | decrement (phase : Bool) | check | finish
  deriving DecidableEq
open Label
instance : Inhabited Label := ⟨field default⟩
instance : Fintype Label where
  elems := (Finset.univ.image field) ∪ {decrement false,decrement true,check,finish}
  complete l := by cases l with
    | field p => simp
    | decrement b => cases b <;> simp
    | check => simp
    | finish => simp

abbrev Config := Cfg (fun _ : Stack => Bool) Label (Option Bool)
def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | field l => TM2ReturnLink.redirect field check (fieldProgram l)
  | decrement b => TM2ReturnLink.redirect decrement finish (counterProgram b)
  | check => .branch (fun v => decide (v = some true))
      (.goto (fun _ => decrement false)) .halt
  | finish => .halt

def tick (c : Config) : Config := (step program c).getD c

def state (phase : Option Label) (source collected temp value outer archive : List Bool)
    (v : Option Bool) : Config :=
  ⟨phase,v,fun k => match k with
    | .inl input => source | .inl count => collected
    | .inl scratch => temp | .inl output => value
    | .inr false => outer | .inr true => archive⟩

def start (word outer archive : List Bool) : Config :=
  TM2ReturnLink.embed field check
    (TM2StackFrame.embed fieldLayout (FieldPrefixMachine.start word) (frame outer archive))

private theorem redirect_supports {L : Type*} (f : L → Label) (ret : Label)
    (s : Stmt (fun _ : Stack => Bool) L (Option Bool)) :
    SupportsStmt Finset.univ (TM2ReturnLink.redirect f ret s) := by
  induction s <;> simp_all [TM2ReturnLink.redirect,SupportsStmt]

theorem supports : Supports program Finset.univ := by
  constructor
  · simp
  · intro l _
    cases l <;> simp [program,redirect_supports,SupportsStmt]

/-- Derive the full successful field workspace, not only its public readout. -/
theorem field_complete (bs suffix : List Bool) :
    ∃ fuel ≤ 3*bs.length.size+7+bs.length*(2*bs.length.size+3),
      FieldPrefixMachine.tick^[fuel]
        (FieldPrefixMachine.start (uniformNatEncode bs.length ++ (bs++suffix))) =
        ⟨none,some true,(FieldReadMachine.config none bs [] suffix [] (some true)).stk⟩ := by
  obtain ⟨k,hk,hp⟩ := FieldPrefixMachine.prefix_run _ bs.length (bs++suffix)
    (uniformNatRead_encode _ _)
  obtain ⟨j,hj,hr⟩ := FieldReadMachine.run bs suffix (some true)
  have hh : (FieldReadMachine.tick^[j]
      (FieldReadMachine.config (some .scan) bs.length.bits [] (bs++suffix) [] (some true))).l = none := by
    rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run FieldReadMachine.program FieldPrefixMachine.program
    FieldPrefixMachine.Label.field FieldPrefixMachine.Label.finish (fun _ => rfl) _ _ hh
  change FieldPrefixMachine.tick^[u] _ = TM2ReturnLink.embed _ _ (FieldReadMachine.tick^[j] _) at he
  rw [hr] at he
  refine ⟨1+(u+k),by omega,?_⟩
  rw [Function.iterate_add_apply FieldPrefixMachine.tick 1,
    Function.iterate_add_apply FieldPrefixMachine.tick u k,hp,he]
  rfl

private theorem field_return (word outer archive : List Bool) (fuel : Nat)
    (c : FieldPrefixMachine.Config)
    (he : FieldPrefixMachine.tick^[fuel] (FieldPrefixMachine.start word) = c)
    (hh : c.l = none) :
    ∃ used ≤ fuel, tick^[used] (start word outer archive) =
      TM2ReturnLink.embed field check (TM2StackFrame.embed fieldLayout c (frame outer archive)) := by
  have hf := TM2StackFrame.run fieldLayout FieldPrefixMachine.program fuel
    (FieldPrefixMachine.start word) (frame outer archive)
  change (TM2ReturnLink.tick fieldProgram)^[fuel] _ =
    TM2StackFrame.embed fieldLayout (FieldPrefixMachine.tick^[fuel] _) _ at hf
  rw [he] at hf
  have hl : ((TM2ReturnLink.tick fieldProgram)^[fuel]
      (TM2StackFrame.embed fieldLayout (FieldPrefixMachine.start word) (frame outer archive))).l = none := by
    rw [hf]; exact hh
  obtain ⟨used,hu,hr⟩ := TM2ReturnLink.run fieldProgram program field check
    (fun _ => rfl) _ _ hl
  rw [hf] at hr
  exact ⟨used,hu,hr⟩

/-- Every raw field call returns with both external stacks intact, including
malformed fields. The complete result carries the original machine state. -/
theorem field_run (word outer archive : List Bool) :
    ∃ fuel ≤ 3*word.length+5+(word.length+1)*(2*word.length+4),
      ∃ c : FieldPrefixMachine.Config, c.l = none ∧
      FieldPrefixMachine.readout c = FieldPrefixMachine.decode word ∧
      tick^[fuel] (start word outer archive) =
        TM2ReturnLink.embed field check (TM2StackFrame.embed fieldLayout c (frame outer archive)) := by
  obtain ⟨j,hj,hh,ho⟩ := FieldPrefixMachine.total_run word
  obtain ⟨k,hk,he⟩ := field_return word outer archive j _ rfl hh
  exact ⟨k,hk.trans hj,_,hh,ho,he⟩

/-- The relocated counter updates the outer stack while retaining the field,
source, collected data and archive in the complete configuration. -/
theorem counter_run (n : Nat) (source collected value archive : List Bool) (v : Option Bool) :
    ∃ fuel ≤ 2*n.size+1,
      tick^[fuel] (state (some (decrement false)) source collected [] value n.bits archive v) =
        state (some finish) source collected [] value (n-1).bits archive (some (decide (n ≠ 0))) := by
  obtain ⟨j,hj,he⟩ := BitCounterMachine.run n source collected v
  have hf := TM2StackFrame.run counterLayout BitCounterMachine.program j
    (BitCounterMachine.config (some false) n.bits [] source collected v) (frame value archive)
  change (TM2ReturnLink.tick counterProgram)^[j] _ =
    TM2StackFrame.embed counterLayout (BitCounterMachine.tick^[j] _) _ at hf
  rw [he] at hf
  have hh : ((TM2ReturnLink.tick counterProgram)^[j]
      (TM2StackFrame.embed counterLayout
        (BitCounterMachine.config (some false) n.bits [] source collected v) (frame value archive))).l = none := by
    rw [hf]; rfl
  obtain ⟨k,hk,hr⟩ := TM2ReturnLink.run counterProgram program decrement finish
    (fun _ => rfl) _ _ hh
  rw [hf] at hr
  have hstart : TM2ReturnLink.embed decrement finish (TM2StackFrame.embed counterLayout
      (BitCounterMachine.config (some false) n.bits [] source collected v) (frame value archive)) =
      state (some (decrement false)) source collected [] value n.bits archive v := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    funext k
    cases k with
    | inl k => cases k <;> simp [TM2StackFrame.embed,TM2StackFrame.data,counterLayout,Equiv.swap_apply_def,BitCounterMachine.config,frame]
    | inr k => cases k <;> simp [TM2StackFrame.embed,TM2StackFrame.data,counterLayout,Equiv.swap_apply_def,BitCounterMachine.config,frame]
  have hend : TM2ReturnLink.embed decrement finish (TM2StackFrame.embed counterLayout
      (BitCounterMachine.config none (n-1).bits [] source collected (some (decide (n ≠ 0))))
      (frame value archive)) =
      state (some finish) source collected [] value (n-1).bits archive (some (decide (n ≠ 0))) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    funext k
    cases k with
    | inl k => cases k <;> simp [TM2StackFrame.embed,TM2StackFrame.data,counterLayout,Equiv.swap_apply_def,BitCounterMachine.config,frame]
    | inr k => cases k <;> simp [TM2StackFrame.embed,TM2StackFrame.data,counterLayout,Equiv.swap_apply_def,BitCounterMachine.config,frame]
  rw [hstart,hend] at hr
  exact ⟨k,hk.trans hj,hr⟩

/-- One successful record iteration executes parsing, validation and outer
count decrement. It retains the field, suffix and archive and clears workspace. -/
theorem run (bs suffix archive : List Bool) (n : Nat) :
    ∃ fuel ≤ 3*bs.length.size+10+bs.length*(2*bs.length.size+3)+2*(n+1).size,
      tick^[fuel] (start (uniformNatEncode bs.length ++ (bs++suffix)) (n+1).bits archive) =
        state none suffix [] [] bs n.bits archive (some true) := by
  obtain ⟨j,hj,hfield⟩ := field_complete bs suffix
  obtain ⟨k,hk,hr⟩ := field_return _ (n+1).bits archive j _ hfield rfl
  have he : TM2ReturnLink.embed field check
      (TM2StackFrame.embed fieldLayout
        (⟨none,some true,(FieldReadMachine.config none bs [] suffix [] (some true)).stk⟩ : FieldPrefixMachine.Config)
        (frame (n+1).bits archive)) =
        state (some check) suffix [] [] bs (n+1).bits archive (some true) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr b => cases b <;> rfl
  rw [he] at hr
  have hs : tick (state (some check) suffix [] [] bs (n+1).bits archive (some true)) =
      state (some (decrement false)) suffix [] [] bs (n+1).bits archive (some true) := rfl
  obtain ⟨u,hu,hc⟩ := counter_run (n+1) suffix [] bs archive (some true)
  simp only [Nat.add_sub_cancel,Nat.add_one_ne_zero,ne_eq,not_false_eq_true,decide_true] at hc
  refine ⟨(1+u)+(k+1),by omega,?_⟩
  rw [Function.iterate_add_apply tick (1+u) (k+1),Function.iterate_succ_apply',hr,hs,
    Function.iterate_add_apply tick 1 u,hc]
  rfl

/-- Rejected raw fields halt before outer decrement and preserve both frames. -/
theorem rejected_run (word outer archive : List Bool) (h : FieldPrefixMachine.decode word = none) :
    ∃ fuel ≤ 3*word.length+6+(word.length+1)*(2*word.length+4),
      let c := tick^[fuel] (start word outer archive)
      c.l = none ∧ c.var ≠ some true ∧ c.stk (.inr false) = outer ∧ c.stk (.inr true) = archive := by
  obtain ⟨j,hj,c,hh,ho,he⟩ := field_run word outer archive
  have hv : c.var ≠ some true := by
    intro hv
    simp [FieldPrefixMachine.readout,hh,hv,h] at ho
  have hs : tick (TM2ReturnLink.embed field check
      (TM2StackFrame.embed fieldLayout c (frame outer archive))) =
      ⟨none,c.var,TM2StackFrame.data fieldLayout c.stk (frame outer archive)⟩ := by
    simp [tick,TM2ReturnLink.embed,TM2StackFrame.embed,hh,program,stepAux,hv]
  refine ⟨j+1,by omega,?_⟩
  rw [Function.iterate_succ_apply',he,hs]
  exact ⟨rfl,hv,rfl,rfl⟩

theorem iteration_control :
    tick^[33] (start [true,true,false,false,true,false,true,true,false]
      [false,false,false,true] [true,false]) =
      state none [true,false] [] [] [false,true] [true,true,true] [true,false] (some true) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr b => cases b <;> rfl

theorem rejection_frame_control :
    let c := tick^[6] (start [true,false,false] [false,false,false,true] [true,false])
    c.l = none ∧ c.var = some false ∧
      c.stk (.inr false) = [false,false,false,true] ∧ c.stk (.inr true) = [true,false] := by decide

theorem zero_counter_control :
    let c := tick^[2] (state (some (decrement false)) [] [] [] [true] [] [true,false] none)
    c.l = none ∧ c.var = some false ∧
      c.stk (.inl output) = [true] ∧ c.stk (.inr true) = [true,false] := by decide

theorem no_alias_control :
    let c := tick^[33] (start [true,true,false,false,true,false,true,true,false]
      [false,false,false,true] [true,false])
    c.stk (.inl output) ≠ c.stk (.inr false) ∧ c.stk (.inr true) ≠ [] := by decide

#print axioms iteration_control
#print axioms rejection_frame_control
#print axioms zero_counter_control
#print axioms no_alias_control
#print axioms supports
#print axioms field_complete
#print axioms field_run
#print axioms counter_run
#print axioms run
#print axioms rejected_run
end ExplainableCrypto.Helios.Computational.RecordFieldStepMachine
