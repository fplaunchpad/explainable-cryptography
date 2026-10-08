import ExplainableCrypto.Helios.Computational.RecordParserMachine

/-! Comparison for the repeated cache scan: retain the query, discard the
candidate, and return in the field parser's finite-memory interface. -/
namespace ExplainableCrypto.Helios.Computational.PreservingCompareMachine
open Turing.TM2

inductive Stack where
  | query | candidate | scratch
  deriving DecidableEq
open Stack
instance : Fintype Stack where
  elems := {Stack.query,candidate,scratch}
  complete k := by cases k <;> simp
inductive Label where
  | scan | restore (equal : Bool) | clear (equal : Bool)
  deriving DecidableEq
open Label
instance : Fintype Label where
  elems := {scan,restore false,restore true,clear false,clear true}
  complete l := by cases l with
    | scan => simp
    | restore b => cases b <;> simp
    | clear b => cases b <;> simp
instance : Inhabited Label := ⟨scan⟩
abbrev Config := Cfg (fun _ : Stack => Bool) Label (Option Bool)

private def compareHead (b : Bool) : Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  .pop candidate (fun _ x => x) <| .branch (fun x => decide (x = some b))
    (.goto (fun _ => scan)) (.goto (fun _ => restore false))

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | scan => .pop query (fun _ x => x) <| .branch Option.isSome
      (.push scratch (fun x => x.getD false) <|
        .branch (fun x => x.getD false) (compareHead true) (compareHead false))
      (.pop candidate (fun _ x => x) <| .goto (fun x => restore (!x.isSome)))
  | restore equal => .pop scratch (fun _ x => x) <| .branch Option.isSome
      (.push query (fun x => x.getD false) (.goto (fun _ => restore equal)))
      (.goto (fun _ => clear equal))
  | clear equal => .pop candidate (fun _ x => x) <| .branch Option.isSome
      (.goto (fun _ => clear equal)) (.load (fun _ => some equal) .halt)

def tick (c : Config) : Config := (Turing.TM2.step program c).getD c

def state (phase : Option Label) (queryWord candidateWord buffer : List Bool)
    (v : Option Bool := none) : Config :=
  ⟨phase,v,fun | .query => queryWord | .candidate => candidateWord | .scratch => buffer⟩

theorem supports : Supports program Finset.univ := by
  constructor
  · simp
  · intro l _
    cases l <;> simp [program,compareHead,SupportsStmt]

private theorem clear_run (xs ys : List Bool) (b : Bool) (v : Option Bool) :
    tick^[ys.length+1] (state (some (clear b)) xs ys [] v) =
      state none xs [] [] (some b) := by
  induction ys generalizing v with
  | nil => simp [tick,state,program]
  | cons y ys ih =>
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply]
    have hs : tick (state (some (clear b)) xs (y::ys) [] v) =
        state (some (clear b)) xs ys [] (some y) := by
      simp [tick,state,program]
      funext k; cases k <;> simp
    rw [hs,ih]

private theorem restore_run (xs ys zs : List Bool) (b : Bool) (v : Option Bool) :
    tick^[zs.length+1] (state (some (restore b)) xs ys zs v) =
      state (some (clear b)) (zs.reverse++xs) ys [] none := by
  induction zs generalizing xs v with
  | nil => simp [tick,state,program]
  | cons z zs ih =>
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply]
    have hs : tick (state (some (restore b)) xs ys (z::zs) v) =
        state (some (restore b)) (z::xs) ys zs (some z) := by
      simp [tick,state,program]
      funext k; cases k <;> simp
    rw [hs,ih]
    simp

private theorem finish_run (xs ys zs : List Bool) (b : Bool) (v : Option Bool) :
    tick^[(ys.length+1)+(zs.length+1)] (state (some (restore b)) xs ys zs v) =
      state none (zs.reverse++xs) [] [] (some b) := by
  rw [Function.iterate_add_apply,restore_run,clear_run]

private theorem scan_empty (ys zs : List Bool) (v : Option Bool) :
    tick (state (some scan) [] ys zs v) =
      state (some (restore (decide (ys = [])))) [] ys.tail zs ys.head? := by
  cases ys <;> simp [tick,state,program]
  all_goals funext k; cases k <;> simp

private theorem scan_cons (a : Bool) (xs ys zs : List Bool) (v : Option Bool) :
    tick (state (some scan) (a::xs) ys zs v) =
      state (some (if ys.head? = some a then scan else restore false))
        xs ys.tail (a::zs) ys.head? := by
  cases ys with
  | nil =>
    cases a <;> simp [tick,state,program,compareHead]
    all_goals funext k; cases k <;> simp
  | cons b ys =>
    cases a <;> cases b <;> simp [tick,state,program,compareHead]
    all_goals funext k; cases k <;> simp

/-- General scan invariant: the consumed query prefix is restored even after
an early mismatch; the candidate is cleared on both outcomes. -/
theorem scan_run (xs ys zs : List Bool) (v : Option Bool) :
    ∃ fuel ≤ 2*xs.length+ys.length+zs.length+3,
      tick^[fuel] (state (some scan) xs ys zs v) =
        state none (zs.reverse++xs) [] [] (some (decide (xs = ys))) := by
  induction xs generalizing ys zs v with
  | nil =>
    refine ⟨((ys.tail.length+1)+(zs.length+1))+1,?_,?_⟩
    · simp only [List.length_nil,Nat.mul_zero,Nat.zero_add,List.length_tail]
      omega
    · rw [Function.iterate_succ_apply,scan_empty,finish_run]
      simp [eq_comm]
  | cons a xs ih =>
    by_cases h : ys.head? = some a
    · cases ys with
      | nil => simp at h
      | cons b ys =>
        have he : b = a := Option.some.inj h
        subst b
        obtain ⟨fuel,hf,hr⟩ := ih ys (a::zs) (some a)
        refine ⟨fuel+1,?_,?_⟩
        · simp only [List.length_cons] at hf ⊢; omega
        · rw [Function.iterate_succ_apply,scan_cons]
          simpa [List.append_assoc] using hr
    · have hne : a::xs ≠ ys := by intro he; rw [←he] at h; exact h rfl
      refine ⟨((ys.tail.length+1)+((a::zs).length+1))+1,?_,?_⟩
      · simp only [List.length_cons,List.length_tail]; omega
      · rw [Function.iterate_succ_apply,scan_cons,if_neg h,finish_run]
        simp [hne,List.append_assoc]

/-- Exact restored query, empty candidate/scratch and correct finite return flag,
for arbitrary words and initial finite memory. -/
theorem run (xs ys : List Bool) (v : Option Bool) :
    ∃ fuel ≤ 2*xs.length+ys.length+3,
      tick^[fuel] (state (some scan) xs ys [] v) =
        state none xs [] [] (some (decide (xs = ys))) := by
  simpa using scan_run xs ys [] v

/-- Full typed-key comparison under the original canonical encoding. -/
theorem key_run {p q : Nat} [NeZero p] [NeZero q]
    (a b : BallotForkPoint (PrimeGroup p q)) :
    ∃ fuel ≤ 3*keyRecordBitBound p+3,
      tick^[fuel] (state (some scan) ((ballotKeyBitCodec p q).encode a)
        ((ballotKeyBitCodec p q).encode b) []) =
      state none ((ballotKeyBitCodec p q).encode a) [] [] (some (decide (a = b))) := by
  obtain ⟨fuel,hf,hr⟩ := run ((ballotKeyBitCodec p q).encode a)
    ((ballotKeyBitCodec p q).encode b) none
  have ha := ballotKeyBits_length_le a
  have hb := ballotKeyBits_length_le b
  refine ⟨fuel,by omega,?_⟩
  simpa only [(BitRecordCodec.injective (ballotKeyBitCodec p q)).eq_iff] using hr

/-- The existing six parser stacks plus one retained-query stack. -/
abbrev ParserStack := RecordParserMachine.Stack ⊕ Unit
abbrev ParserConfig := Cfg (fun _ : ParserStack => Bool) Label (Option Bool)
inductive Frame where
  | input | count | outer | archive
  deriving DecidableEq

def layout : Stack ⊕ Frame ≃ ParserStack where
  toFun
    | .inl .query => .inr ()
    | .inl .candidate => .inl (.inl .output)
    | .inl .scratch => .inl (.inl .scratch)
    | .inr .input => .inl (.inl .input)
    | .inr .count => .inl (.inl .count)
    | .inr .outer => .inl (.inr false)
    | .inr .archive => .inl (.inr true)
  invFun
    | .inr _ => .inl .query
    | .inl (.inl .output) => .inl .candidate
    | .inl (.inl .scratch) => .inl .scratch
    | .inl (.inl .input) => .inr .input
    | .inl (.inl .count) => .inr .count
    | .inl (.inr false) => .inr .outer
    | .inl (.inr true) => .inr .archive
  left_inv x := by rcases x with (x|x) <;> cases x <;> rfl
  right_inv x := by
    rcases x with ((x|b)|⟨⟩)
    · cases x <;> rfl
    · cases b <;> rfl
    · rfl

def parserProgram (l : Label) := TM2StackFrame.relocate layout (program l)
def parserTick (c : ParserConfig) := (Turing.TM2.step parserProgram c).getD c

def parserState (phase : Option Label) (q source count temp value outer archive : List Bool)
    (v : Option Bool) : ParserConfig :=
  ⟨phase,v,fun
    | .inl k => (RecordFieldStepMachine.state none source count temp value outer archive v).stk k
    | .inr _ => q⟩

private def frame (source count outer archive : List Bool) : Frame → List Bool
  | .input => source | .count => count | .outer => outer | .archive => archive

private theorem embed_state (phase : Option Label)
    (q source count temp value outer archive : List Bool) (v : Option Bool) :
    TM2StackFrame.embed layout (state phase q value temp v) (frame source count outer archive) =
      parserState phase q source count temp value outer archive v := by
  change (⟨_,_,_⟩ : ParserConfig) = ⟨_,_,_⟩
  congr 1
  funext k
  rcases k with ((k|b)|⟨⟩)
  · cases k <;> rfl
  · cases b <;> rfl
  · rfl

/-- The concrete parser layout preserves the input suffix, collected count,
outer counter and archive; output and scratch are empty for the next call. -/
theorem parser_run (q candidate source count outer archive : List Bool) (v : Option Bool) :
    ∃ fuel ≤ 2*q.length+candidate.length+3,
      parserTick^[fuel] (parserState (some scan) q source count [] candidate outer archive v) =
        parserState none q source count [] [] outer archive (some (decide (q = candidate))) := by
  obtain ⟨fuel,hf,hr⟩ := run q candidate v
  have he := TM2StackFrame.run layout program fuel (state (some scan) q candidate [] v)
    (frame source count outer archive)
  change parserTick^[fuel] _ = TM2StackFrame.embed layout (tick^[fuel] _) _ at he
  rw [hr,embed_state,embed_state] at he
  exact ⟨fuel,hf,he⟩

theorem parser_supports : Supports parserProgram Finset.univ := by
  constructor
  · simp
  · intro l _
    exact (TM2StackFrame.supports layout Finset.univ (program l)).mpr (supports.2 l (by simp))

/-- Equality restores the original nonpalindromic query in full. -/
theorem equal_control :
    ∃ fuel ≤ 12, tick^[fuel] (state (some scan) [true,false,false] [true,false,false] []) =
      state none [true,false,false] [] [] (some true) := by
  exact run [true,false,false] [true,false,false] none

/-- An early mismatch restores the consumed prefix and clears a longer tail. -/
theorem mismatch_control :
    ∃ fuel ≤ 14, tick^[fuel]
      (state (some scan) [true,false,true] [true,true,false,false,false] []) =
      state none [true,false,true] [] [] (some false) := by
  exact run [true,false,true] [true,true,false,false,false] none

/-- Neither ordering of a strict prefix is equality; both queries survive. -/
theorem prefix_control :
    (∃ fuel ≤ 7, tick^[fuel] (state (some scan) [true] [true,false] []) =
      state none [true] [] [] (some false)) ∧
    (∃ fuel ≤ 8, tick^[fuel] (state (some scan) [true,false] [true] []) =
      state none [true,false] [] [] (some false)) := by
  exact ⟨run [true] [true,false] none,run [true,false] [true] none⟩

/-- Literal surrounding parser data cannot be mistaken for query workspace. -/
theorem parser_frame_control :
    ∃ fuel ≤ 9, parserTick^[fuel]
      (parserState (some scan) [true,false] [false,true] [true] [] [true,true]
        [false,false,true] [true,false,true] (some true)) =
      parserState none [true,false] [false,true] [true] [] []
        [false,false,true] [true,false,true] (some false) := by
  exact parser_run [true,false] [true,true] [false,true] [true]
    [false,false,true] [true,false,true] (some true)

#print axioms supports
#print axioms scan_run
#print axioms run
#print axioms key_run
#print axioms parser_run
#print axioms parser_supports
#print axioms equal_control
#print axioms mismatch_control
#print axioms prefix_control
#print axioms parser_frame_control

end ExplainableCrypto.Helios.Computational.PreservingCompareMachine
