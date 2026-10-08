import ExplainableCrypto.Helios.Computational.TM2InputArchive

/-! Preserve original field framing in the archive and clear output for reuse. -/
namespace ExplainableCrypto.Helios.Computational.ArchivedFieldMachine
open Turing.TM2
abbrev Stack := RecordFieldStepMachine.Stack

theorem eligible : ∀ l, TM2InputArchive.Eligible (RecordFieldStepMachine.program l) := by
  intro l
  fin_cases l
  all_goals simp [RecordFieldStepMachine.program,RecordFieldStepMachine.fieldProgram,
    RecordFieldStepMachine.counterProgram,RecordFieldStepMachine.fieldLayout,
    RecordFieldStepMachine.counterLayout,TM2StackFrame.relocate,TM2ReturnLink.redirect,
    FieldPrefixMachine.program,FieldReadMachine.program,BitCounterMachine.program,
    NatPrefixMachine.program,TM2InputArchive.Eligible,Equiv.swap_apply_def,
    TM2InputArchive.src,TM2InputArchive.dst]
  all_goals exact True.intro

def recordedProgram (l : RecordFieldStepMachine.Label) :=
  TM2InputArchive.record (RecordFieldStepMachine.program l)


private theorem start_archive (word outer archive : List Bool) :
    TM2InputArchive.withArchive (RecordFieldStepMachine.start word outer []) archive =
      RecordFieldStepMachine.start word outer archive := by
  change (⟨_,_,_⟩ : RecordFieldStepMachine.Config) = ⟨_,_,_⟩
  congr 1
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr b => cases b <;> rfl

private theorem state_archive (l : Option RecordFieldStepMachine.Label)
    (source collected temp value outer old archive : List Bool) (v : Option Bool) :
    TM2InputArchive.withArchive (RecordFieldStepMachine.state l source collected temp value outer old v)
      archive = RecordFieldStepMachine.state l source collected temp value outer archive v := by
  change (⟨_,_,_⟩ : RecordFieldStepMachine.Config) = ⟨_,_,_⟩
  congr 1
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr b => cases b <;> rfl

/-- A successful iteration records the original length prefix and payload,
with exactly the original fuel. The old archive remains as an intact suffix. -/
theorem recorded_run (bs suffix archive : List Bool) (n : Nat) :
    ∃ fuel ≤ 3*bs.length.size+10+bs.length*(2*bs.length.size+3)+2*(n+1).size,
      (TM2ReturnLink.tick recordedProgram)^[fuel]
        (RecordFieldStepMachine.start (uniformNatEncode bs.length ++ (bs++suffix)) (n+1).bits archive) =
        RecordFieldStepMachine.state none suffix [] [] bs n.bits
          ((uniformNatEncode bs.length ++ bs).reverse ++ archive) (some true) := by
  obtain ⟨j,hj,he⟩ := RecordFieldStepMachine.run bs suffix [] n
  obtain ⟨consumed,hc,hr⟩ := TM2InputArchive.run RecordFieldStepMachine.program eligible j
    (RecordFieldStepMachine.start (uniformNatEncode bs.length ++ (bs++suffix)) (n+1).bits []) archive
  change _ = consumed ++ (RecordFieldStepMachine.tick^[j] _).stk TM2InputArchive.src at hc
  change (TM2ReturnLink.tick recordedProgram)^[j] _ =
    TM2InputArchive.withArchive (RecordFieldStepMachine.tick^[j] _) _ at hr
  rw [he] at hc hr
  change uniformNatEncode bs.length ++ (bs++suffix) = consumed ++ suffix at hc
  have hcons : consumed = uniformNatEncode bs.length ++ bs :=
    List.append_cancel_right (by simpa only [List.append_assoc] using hc.symm)
  rw [start_archive,state_archive,hcons] at hr
  exact ⟨j,hj,hr⟩

inductive Label where
  | step (phase : RecordFieldStepMachine.Label) | done | clear
  deriving DecidableEq
open Label
instance : Inhabited Label := ⟨step default⟩
instance : Fintype Label where
  elems := (Finset.univ.image step) ∪ {done,clear}
  complete l := by cases l <;> simp

abbrev Config := Cfg (fun _ : Stack => Bool) Label (Option Bool)
def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .step l => TM2ReturnLink.redirect step done (recordedProgram l)
  | done => .branch (fun v => decide (v = some true)) (.goto (fun _ => clear)) .halt
  | clear => .pop (.inl .output) (fun _ b => b) <| .branch Option.isSome
      (.goto (fun _ => clear)) (.load (fun _ => some true) .halt)

def tick (c : Config) : Config := (Turing.TM2.step program c).getD c

def state (phase : Option Label) (source collected temp value outer archive : List Bool)
    (v : Option Bool) : Config :=
  ⟨phase,v,(RecordFieldStepMachine.state none source collected temp value outer archive v).stk⟩
def start (word outer archive : List Bool) : Config :=
  TM2ReturnLink.embed step done (RecordFieldStepMachine.start word outer archive)

private theorem redirect_supports {L : Type*} (f : L → Label) (ret : Label)
    (s : Stmt (fun _ : Stack => Bool) L (Option Bool)) :
    SupportsStmt Finset.univ (TM2ReturnLink.redirect f ret s) := by
  induction s <;> simp_all [TM2ReturnLink.redirect,SupportsStmt]

theorem supports : Supports program Finset.univ := by
  constructor
  · simp
  · intro l _
    cases l <;> simp [program,redirect_supports,SupportsStmt]

private theorem clear_run (source outer archive value : List Bool) (v : Option Bool) :
    tick^[value.length+1] (state (some clear) source [] [] value outer archive v) =
      state none source [] [] [] outer archive (some true) := by
  induction value generalizing v with
  | nil => simp [tick,state,program,RecordFieldStepMachine.state,stepAux]
  | cons b bs ih =>
    have hs : tick (state (some clear) source [] [] (b::bs) outer archive v) =
        state (some clear) source [] [] bs outer archive (some b) := by
      simp [tick,state,program,RecordFieldStepMachine.state,stepAux]
      funext k
      cases k with
      | inl k => cases k <;> simp
      | inr b => cases b <;> simp
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,hs,ih]

/-- Archive one original field frame and clear every work stack for reuse,
while actually executing the count decrement and final cleanup. -/
theorem run (bs suffix archive : List Bool) (n : Nat) :
    ∃ fuel ≤ 3*bs.length.size+12+bs.length*(2*bs.length.size+4)+2*(n+1).size,
      tick^[fuel] (start (uniformNatEncode bs.length ++ (bs++suffix)) (n+1).bits archive) =
        state none suffix [] [] [] n.bits
          ((uniformNatEncode bs.length ++ bs).reverse ++ archive) (some true) := by
  obtain ⟨j,hj,he⟩ := recorded_run bs suffix archive n
  have hh : ((TM2ReturnLink.tick recordedProgram)^[j]
      (RecordFieldStepMachine.start (uniformNatEncode bs.length ++ (bs++suffix)) (n+1).bits archive)).l = none := by
    rw [he]; rfl
  obtain ⟨k,hk,hr⟩ := TM2ReturnLink.run recordedProgram program step done (fun _ => rfl) _ _ hh
  rw [he] at hr
  change tick^[k] (start _ _ _) = state (some done) suffix [] [] bs n.bits
    ((uniformNatEncode bs.length ++ bs).reverse ++ archive) (some true) at hr
  have hs : tick (state (some done) suffix [] [] bs n.bits
      ((uniformNatEncode bs.length ++ bs).reverse ++ archive) (some true)) =
      state (some clear) suffix [] [] bs n.bits
        ((uniformNatEncode bs.length ++ bs).reverse ++ archive) (some true) := rfl
  refine ⟨(bs.length+1)+(k+1),?_,?_⟩
  · simp only [Nat.mul_add] at hj ⊢
    omega
  · rw [Function.iterate_add_apply tick (bs.length+1) (k+1),Function.iterate_succ_apply' tick k,hr,hs,clear_run]


/-- Rejection preserves original control/count and records only the consumed
prefix; cleanup cannot turn a rejected field into success. -/
theorem rejected_run (word outer archive : List Bool) (h : FieldPrefixMachine.decode word = none) :
    ∃ fuel ≤ 3*word.length+7+(word.length+1)*(2*word.length+4),
      let out := tick^[fuel] (start word outer archive)
      out.l = none ∧ out.var ≠ some true ∧ out.stk (.inr false) = outer ∧
      ∃ consumed, word = consumed ++ out.stk TM2InputArchive.src ∧
        out.stk TM2InputArchive.dst = consumed.reverse ++ archive := by
  obtain ⟨j,hj,hh,hv,ho,_⟩ := RecordFieldStepMachine.rejected_run word outer [] h
  let c := RecordFieldStepMachine.tick^[j] (RecordFieldStepMachine.start word outer [])
  change c.l = none at hh
  change c.var ≠ some true at hv
  change c.stk (.inr false) = outer at ho
  obtain ⟨consumed,hc,hr⟩ := TM2InputArchive.run RecordFieldStepMachine.program eligible j
    (RecordFieldStepMachine.start word outer []) archive
  change word = consumed ++ c.stk TM2InputArchive.src at hc
  change (TM2ReturnLink.tick recordedProgram)^[j] _ =
    TM2InputArchive.withArchive c (consumed.reverse++archive) at hr
  rw [start_archive] at hr
  have hhalt : ((TM2ReturnLink.tick recordedProgram)^[j]
      (RecordFieldStepMachine.start word outer archive)).l = none := by
    rw [hr]; exact hh
  obtain ⟨k,hk,he⟩ := TM2ReturnLink.run recordedProgram program step done (fun _ => rfl) _ _ hhalt
  rw [hr] at he
  change tick^[k] (start word outer archive) =
    TM2ReturnLink.embed step done (TM2InputArchive.withArchive c (consumed.reverse++archive)) at he
  have hs : tick (TM2ReturnLink.embed step done
      (TM2InputArchive.withArchive c (consumed.reverse++archive))) =
      ⟨none,c.var,(TM2InputArchive.withArchive c (consumed.reverse++archive)).stk⟩ := by
    simp [tick,TM2ReturnLink.embed,TM2InputArchive.withArchive,hh,program,stepAux,hv]
  refine ⟨k+1,by omega,?_⟩
  change (tick^[k+1] _).l = none ∧ _
  rw [Function.iterate_succ_apply',he,hs]
  refine ⟨rfl,hv,?_,consumed,?_,?_⟩
  · simpa [TM2InputArchive.withArchive,TM2InputArchive.dst] using ho
  · simpa [TM2InputArchive.withArchive,TM2InputArchive.src,TM2InputArchive.dst] using hc
  · simp [TM2InputArchive.withArchive]

theorem iteration_control :
    tick^[37] (start [true,true,false,false,true,false,true,true,false]
      [false,false,false,true] [true,false]) =
      state none [true,false] [] [] [] [true,true,true]
        [true,false,true,false,false,true,true,true,false] (some true) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr b => cases b <;> rfl

theorem empty_field_control :
    tick^[13] (start [false,true,false] [true] [true,false]) =
      state none [true,false] [] [] [] [] [false,true,false] (some true) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr b => cases b <;> rfl

theorem absent_bit_control :
    let c := tick^[4] (start [] [true] [true,false])
    c.l = none ∧ c.var = some false ∧ c.stk TM2InputArchive.dst = [true,false] := by decide

theorem rejection_control :
    let c := tick^[7] (start [true,false,false] [true] [true,false])
    c.l = none ∧ c.var = some false ∧ c.stk (.inr false) = [true] ∧
      c.stk TM2InputArchive.dst = [false,false,true,true,false] := by decide

theorem no_boundary_loss_control :
    (tick^[13] (start [false,true,false] [true] [true,false])).stk TM2InputArchive.dst ≠
      [true,false] := by decide

#print axioms eligible
#print axioms recorded_run
#print axioms supports
#print axioms run
#print axioms rejected_run
#print axioms iteration_control
#print axioms empty_field_control
#print axioms absent_bit_control
#print axioms rejection_control
#print axioms no_boundary_loss_control
end ExplainableCrypto.Helios.Computational.ArchivedFieldMachine
