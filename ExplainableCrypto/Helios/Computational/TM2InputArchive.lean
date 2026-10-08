import ExplainableCrypto.Helios.Computational.RecordFieldStepMachine

/-! Record consumed input bits on the existing archive stack. Structural
eligibility ensures that the original control never depends on this archive. -/
namespace ExplainableCrypto.Helios.Computational.TM2InputArchive
open Turing.TM2
abbrev Stack := RecordFieldStepMachine.Stack
abbrev src : Stack := .inl .input
abbrev dst : Stack := .inr true
variable {L : Type*}

/-- Input only shrinks; archive is inaccessible; input pops store their head. -/
def Eligible : Stmt (fun _ : Stack => Bool) L (Option Bool) → Prop
  | .push k _ s => k ≠ src ∧ k ≠ dst ∧ Eligible s
  | .peek k _ s => k ≠ dst ∧ Eligible s
  | .pop k f s => k ≠ dst ∧ (k = src → ∀ v b, f v b = b) ∧ Eligible s
  | .load _ s => Eligible s
  | .branch _ a b => Eligible a ∧ Eligible b
  | .goto _ => True
  | .halt => True

def record : Stmt (fun _ : Stack => Bool) L (Option Bool) →
    Stmt (fun _ : Stack => Bool) L (Option Bool)
  | .push k f s => .push k f (record s)
  | .peek k f s => .peek k f (record s)
  | .pop k f s => .pop k f <| if k = src then
      .branch Option.isSome (.push dst (fun v => v.getD false) (record s)) (record s)
      else record s
  | .load f s => .load f (record s)
  | .branch f a b => .branch f (record a) (record b)
  | .goto f => .goto f
  | .halt => .halt

def withArchive (c : Cfg (fun _ : Stack => Bool) L (Option Bool)) (a : List Bool) :=
  { c with stk := Function.update c.stk dst a }

private theorem updates (tapes : Stack → List Bool) (k : Stack) (h : k ≠ dst)
    (word a : List Bool) :
    Function.update (Function.update tapes dst a) k word =
      Function.update (Function.update tapes k word) dst a := by
  funext j
  by_cases hk : j = k <;> by_cases hd : j = dst <;> simp_all [Function.update]

/-- Complete statement correspondence, with exact consumed-prefix accounting. -/
theorem statement (s : Stmt (fun _ : Stack => Bool) L (Option Bool)) (hs : Eligible s)
    (v : Option Bool) (tapes : Stack → List Bool) (archive : List Bool) :
    ∃ consumed,
      tapes src = consumed ++ (stepAux s v tapes).stk src ∧
      stepAux (record s) v (Function.update tapes dst archive) =
        withArchive (stepAux s v tapes) (consumed.reverse ++ archive) := by
  induction s generalizing v tapes archive with
  | push k f s ih =>
    rcases hs with ⟨hk,hd,hs⟩
    obtain ⟨bs,hb,he⟩ := ih hs v (Function.update tapes k (f v::tapes k)) archive
    refine ⟨bs,?_,?_⟩
    · simpa [stepAux,Function.update,Ne.symm hk] using hb
    · simpa only [record,stepAux,Function.update_of_ne hd,updates tapes k hd] using he
  | peek k f s ih =>
    rcases hs with ⟨hd,hs⟩
    simpa only [record,stepAux,Function.update_of_ne hd] using
      ih hs (f v (tapes k).head?) tapes archive
  | pop k f s ih =>
    rcases hs with ⟨hd,hf,hs⟩
    by_cases hk : k = src
    · subst k
      cases hw : tapes src with
      | nil =>
        obtain ⟨bs,hb,he⟩ := ih hs none (Function.update tapes src []) archive
        refine ⟨bs,?_,?_⟩
        · simpa [stepAux,hw,hf rfl,Function.update] using hb
        · simpa [record,stepAux,hw,hf rfl,Function.update_of_ne hd,updates tapes src hd] using he
      | cons b rest =>
        obtain ⟨bs,hb,he⟩ := ih hs (some b) (Function.update tapes src rest) (b::archive)
        refine ⟨b::bs,?_,?_⟩
        · simpa [stepAux,hw,hf rfl,Function.update] using congrArg (List.cons b) hb
        · simpa [record,stepAux,hw,hf rfl,Function.update_of_ne hd,
            updates tapes src hd,Function.update_idem] using he
    · obtain ⟨bs,hb,he⟩ := ih hs (f v (tapes k).head?)
        (Function.update tapes k (tapes k).tail) archive
      refine ⟨bs,?_,?_⟩
      · simpa [stepAux,Function.update,Ne.symm hk] using hb
      · simpa only [record,stepAux,if_neg hk,Function.update_of_ne hd,updates tapes k hd] using he
  | load f s ih => exact ih hs _ _ _
  | branch f a b ia ib =>
    cases h : f v <;> simp only [record,stepAux,h,cond_false,cond_true]
    · exact ib hs.2 _ _ _
    · exact ia hs.1 _ _ _
  | goto f => exact ⟨[],rfl,rfl⟩
  | halt => exact ⟨[],rfl,rfl⟩

/-- Every tick consumes a prefix and records it while preserving original control. -/
theorem tick (p : L → Stmt (fun _ : Stack => Bool) L (Option Bool))
    (hp : ∀ l, Eligible (p l)) (c : Cfg (fun _ : Stack => Bool) L (Option Bool))
    (archive : List Bool) :
    ∃ consumed, c.stk src = consumed ++ (TM2ReturnLink.tick p c).stk src ∧
      TM2ReturnLink.tick (fun l => record (p l)) (withArchive c archive) =
        withArchive (TM2ReturnLink.tick p c) (consumed.reverse++archive) := by
  cases c with
  | mk l v tapes =>
    cases l with
    | none => exact ⟨[],rfl,rfl⟩
    | some l => exact statement (p l) (hp l) v tapes archive

/-- Exact prefix/archive accounting for any run length, including rejected runs. -/
theorem run (p : L → Stmt (fun _ : Stack => Bool) L (Option Bool))
    (hp : ∀ l, Eligible (p l)) (fuel : Nat)
    (c : Cfg (fun _ : Stack => Bool) L (Option Bool)) (archive : List Bool) :
    ∃ consumed, c.stk src = consumed ++ ((TM2ReturnLink.tick p)^[fuel] c).stk src ∧
      (TM2ReturnLink.tick (fun l => record (p l)))^[fuel] (withArchive c archive) =
        withArchive ((TM2ReturnLink.tick p)^[fuel] c) (consumed.reverse++archive) := by
  induction fuel generalizing c archive with
  | zero => exact ⟨[],rfl,rfl⟩
  | succ fuel ih =>
    obtain ⟨first,hfirst,he⟩ := tick p hp c archive
    obtain ⟨rest,hrest,hr⟩ := ih (TM2ReturnLink.tick p c) (first.reverse++archive)
    refine ⟨first++rest,?_,?_⟩
    · rw [hfirst,hrest,Function.iterate_succ_apply,List.append_assoc]
    · rw [Function.iterate_succ_apply,he,hr]
      simp [Function.iterate_succ_apply,List.reverse_append,List.append_assoc]

theorem supports (S : Finset L) (s : Stmt (fun _ : Stack => Bool) L (Option Bool)) :
    SupportsStmt S (record s) ↔ SupportsStmt S s := by
  induction s with
  | push k f s ih => exact ih
  | peek k f s ih => exact ih
  | pop k f s ih => by_cases h : k = src <;> simp [record,SupportsStmt,h,ih]
  | load f s ih => exact ih
  | branch f a b ia ib => simp [record,SupportsStmt,ia,ib]
  | goto f => rfl
  | halt => rfl

private def archiveSensitive : Stmt (fun _ : Stack => Bool) Bool (Option Bool) :=
  .pop src (fun _ b => b) <| .peek dst (fun _ b => b) <|
    .branch (fun v => v.getD false) (.goto (fun _ => true)) (.goto (fun _ => false))

/-- Archive independence is load-bearing: reading recorded data changes control. -/
theorem archive_dependency_control :
    (stepAux archiveSensitive none (fun k => if k = src then [true] else [])).l = some false ∧
    (stepAux (record archiveSensitive) none (fun k => if k = src then [true] else [])).l = some true := by
  decide

theorem archive_sensitive_ineligible : ¬ Eligible archiveSensitive := by
  simp [archiveSensitive,Eligible]

#print axioms archive_dependency_control
#print axioms archive_sensitive_ineligible
#print axioms statement
#print axioms tick
#print axioms run
#print axioms supports
end ExplainableCrypto.Helios.Computational.TM2InputArchive
