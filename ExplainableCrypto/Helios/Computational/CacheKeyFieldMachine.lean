import ExplainableCrypto.Helios.Computational.PreservingCompareMachine

/-! Execute the original cache-entry pair header and key field, then compare
while retaining the query and the scalar-answer suffix. -/
namespace ExplainableCrypto.Helios.Computational.CacheKeyFieldMachine
open Turing.TM2
abbrev Stack := PreservingCompareMachine.ParserStack

def fieldLayout : NatPrefixMachine.Stack ⊕ (Bool ⊕ Unit) ≃ Stack :=
  (Equiv.sumAssoc NatPrefixMachine.Stack Bool Unit).symm

def fieldFrame (q outer archive : List Bool) : Bool ⊕ Unit → List Bool
  | .inl false => outer | .inl true => archive | .inr _ => q

def fieldProgram (l : FieldPrefixMachine.Label) :=
  TM2StackFrame.relocate fieldLayout (FieldPrefixMachine.program l)

inductive Label where
  | h0 | h1 | h2 | h3 | h4
  | field (l : FieldPrefixMachine.Label)
  | compare (l : PreservingCompareMachine.Label)
  | check | finish
  deriving DecidableEq
open Label
instance : Inhabited Label := ⟨h0⟩
instance : Fintype Label where
  elems := (Finset.univ.image field) ∪ (Finset.univ.image compare) ∪ {h0,h1,h2,h3,h4,check,finish}
  complete l := by cases l <;> simp
abbrev Config := Cfg (fun _ : Stack => Bool) Label (Option Bool)

private def invalid : Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  .load (fun _ => none) .halt
private def expect (b : Bool) (next : Label) : Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  .pop (.inl (.inl .input)) (fun _ x => x) <| .branch (fun x => decide (x = some b))
    (.load (fun _ => none) (.goto (fun _ => next))) invalid

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | h0 => expect true h1
  | h1 => expect true h2
  | h2 => expect false h3
  | h3 => expect false h4
  | h4 => expect true (field default)
  | field l => TM2ReturnLink.redirect field check (fieldProgram l)
  | .compare l => TM2ReturnLink.redirect compare finish (PreservingCompareMachine.parserProgram l)
  | check => .branch (fun x => decide (x = some true))
      (.goto (fun _ => compare .scan)) invalid
  | finish => .halt

def tick (c : Config) : Config := (Turing.TM2.step program c).getD c

def state (phase : Option Label) (q source count temp value outer archive : List Bool)
    (v : Option Bool) : Config :=
  ⟨phase,v,(PreservingCompareMachine.parserState none q source count temp value outer archive v).stk⟩
def start (q word outer archive : List Bool) : Config :=
  state (some h0) q word [] [] [] outer archive none

private theorem redirect_supports {L : Type*} (f : L → Label) (ret : Label)
    (s : Stmt (fun _ : Stack => Bool) L (Option Bool)) :
    SupportsStmt Finset.univ (TM2ReturnLink.redirect f ret s) := by
  induction s <;> simp_all [TM2ReturnLink.redirect,SupportsStmt]

theorem supports : Supports program Finset.univ := by
  constructor
  · simp
  · intro l _
    cases l <;> simp [program,expect,invalid,redirect_supports,SupportsStmt]

private theorem header_step (l next : Label) (b : Bool)
    (hp : program l = expect b next) (q rest outer archive : List Bool) (v : Option Bool) :
    tick (state (some l) q (b::rest) [] [] [] outer archive v) =
      state (some next) q rest [] [] [] outer archive none := by
  simp [tick,state,hp,PreservingCompareMachine.parserState,RecordFieldStepMachine.state]
  simp [expect,invalid]
  funext k
  rcases k with ((k|b)|⟨⟩)
  · cases k <;> simp
  · cases b <;> simp
  · simp

/-- The original E(2) count header is consumed by five actual transitions. -/
theorem header_run (q word outer archive : List Bool) :
    tick^[5] (start q (uniformNatEncode 2++word) outer archive) =
      TM2ReturnLink.embed field check (TM2StackFrame.embed fieldLayout
        (FieldPrefixMachine.start word) (fieldFrame q outer archive)) := by
  rw [show uniformNatEncode 2 = [true,true,false,false,true] by decide]
  change tick (tick (tick (tick (tick (state (some h0) q
    (true::true::false::false::true::word) [] [] [] outer archive none))))) = _
  rw [header_step h0 h1 true rfl,header_step h1 h2 true rfl,
    header_step h2 h3 false rfl,header_step h3 h4 false rfl,
    header_step h4 (field default) true rfl]
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  rcases k with ((k|b)|⟨⟩)
  · cases k <;> rfl
  · cases b <;> rfl
  · rfl

private theorem field_return (q word outer archive : List Bool) (fuel : Nat)
    (c : FieldPrefixMachine.Config)
    (hr : FieldPrefixMachine.tick^[fuel] (FieldPrefixMachine.start word) = c)
    (hh : c.l = none) :
    ∃ used ≤ fuel, tick^[used]
      (TM2ReturnLink.embed field check (TM2StackFrame.embed fieldLayout
        (FieldPrefixMachine.start word) (fieldFrame q outer archive))) =
      TM2ReturnLink.embed field check (TM2StackFrame.embed fieldLayout c (fieldFrame q outer archive)) := by
  have he := TM2StackFrame.run fieldLayout FieldPrefixMachine.program fuel
    (FieldPrefixMachine.start word) (fieldFrame q outer archive)
  change (TM2ReturnLink.tick fieldProgram)^[fuel] _ =
    TM2StackFrame.embed fieldLayout (FieldPrefixMachine.tick^[fuel] _) _ at he
  rw [hr] at he
  have hl : ((TM2ReturnLink.tick fieldProgram)^[fuel]
      (TM2StackFrame.embed fieldLayout (FieldPrefixMachine.start word) (fieldFrame q outer archive))).l = none := by
    rw [he]; exact hh
  obtain ⟨used,hu,hf⟩ := TM2ReturnLink.run fieldProgram program field check (fun _ => rfl) _ _ hl
  rw [he] at hf
  exact ⟨used,hu,hf⟩

/-- Complete pair-header/key-field execution, with the actual parser-derived
handoff, preserved query/answer suffix and equality flag. -/
theorem run (q key suffix outer archive : List Bool) :
    ∃ fuel ≤ 3*key.length.size+17+key.length*(2*key.length.size+4)+2*q.length,
      tick^[fuel] (start q
        (uniformNatEncode 2++(uniformNatEncode key.length++(key++suffix))) outer archive) =
      state none q suffix [] [] [] outer archive (some (decide (q = key))) := by
  obtain ⟨j,hj,hfield⟩ := RecordFieldStepMachine.field_complete key suffix
  obtain ⟨u,hu,he⟩ := field_return q _ outer archive j _ hfield rfl
  have hend : TM2ReturnLink.embed field check
      (TM2StackFrame.embed fieldLayout
        (⟨none,some true,(FieldReadMachine.config none key [] suffix [] (some true)).stk⟩ :
          FieldPrefixMachine.Config) (fieldFrame q outer archive)) =
      state (some check) q suffix [] [] key outer archive (some true) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    funext k
    rcases k with ((k|b)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl
  rw [hend] at he
  have hc : tick (state (some check) q suffix [] [] key outer archive (some true)) =
      TM2ReturnLink.embed compare finish
        (PreservingCompareMachine.parserState (some .scan) q suffix [] [] key outer archive (some true)) := rfl
  obtain ⟨j',hj',hcompare⟩ := PreservingCompareMachine.parser_run q key suffix [] outer archive (some true)
  have hhalt : (PreservingCompareMachine.parserTick^[j']
      (PreservingCompareMachine.parserState (some .scan) q suffix [] [] key outer archive (some true))).l = none := by
    rw [hcompare]; rfl
  obtain ⟨u',hu',he'⟩ := TM2ReturnLink.run PreservingCompareMachine.parserProgram program compare finish
    (fun _ => rfl) _ _ hhalt
  change tick^[u'] _ = TM2ReturnLink.embed compare finish (PreservingCompareMachine.parserTick^[j'] _) at he'
  rw [hcompare] at he'
  refine ⟨1+(u'+(1+(u+5))),by simp only [Nat.mul_add] at hj ⊢; omega,?_⟩
  rw [Function.iterate_add_apply tick 1,Function.iterate_add_apply tick u',
    Function.iterate_add_apply tick 1,Function.iterate_add_apply tick u,header_run,he,Function.iterate_one,hc,he']
  rfl

/-- Malformed key fields return a distinct invalid flag after the original pair
header. Query, outer count and archive remain unchanged. -/
theorem rejected_run (q word outer archive : List Bool)
    (hd : FieldPrefixMachine.decode word = none) :
    ∃ fuel ≤ 3*word.length+11+(word.length+1)*(2*word.length+4),
      let c := tick^[fuel] (start q (uniformNatEncode 2++word) outer archive)
      c.l = none ∧ c.var = none ∧ c.stk (.inr ()) = q ∧
        c.stk (.inl (.inr false)) = outer ∧ c.stk (.inl (.inr true)) = archive := by
  obtain ⟨j,hj,hh,ho⟩ := FieldPrefixMachine.total_run word
  let c := FieldPrefixMachine.tick^[j] (FieldPrefixMachine.start word)
  change c.l = none at hh
  change FieldPrefixMachine.readout c = _ at ho
  have hv : c.var ≠ some true := by
    intro hv
    simp [FieldPrefixMachine.readout,hh,hv,hd] at ho
  obtain ⟨u,hu,he⟩ := field_return q word outer archive j c rfl hh
  have hs : tick (TM2ReturnLink.embed field check
      (TM2StackFrame.embed fieldLayout c (fieldFrame q outer archive))) =
      ⟨none,none,(TM2StackFrame.embed fieldLayout c (fieldFrame q outer archive)).stk⟩ := by
    simp [tick,program,invalid,TM2ReturnLink.embed,TM2StackFrame.embed,hh,hv]
  refine ⟨1+(u+5),by omega,?_⟩
  rw [Function.iterate_add_apply tick 1,Function.iterate_add_apply tick u,header_run,he]
  simp only [Function.iterate_one]
  rw [hs]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Every wrong or truncated original pair-count header halts as invalid. -/
theorem header_rejected (q word outer archive : List Bool)
    (h : word.take 5 ≠ uniformNatEncode 2) :
    let c := tick^[5] (start q word outer archive)
    c.l = none ∧ c.var = none ∧ c.stk (.inr ()) = q ∧
      c.stk (.inl (.inr false)) = outer ∧ c.stk (.inl (.inr true)) = archive := by
  rw [show uniformNatEncode 2 = [true,true,false,false,true] by decide] at h
  rcases word with (_|⟨b0,(_|⟨b1,(_|⟨b2,(_|⟨b3,(_|⟨b4,rest⟩)⟩)⟩)⟩)⟩)
  all_goals repeat' first | cases b0 | cases b1 | cases b2 | cases b3 | cases b4
  all_goals simp_all [start,state,tick,program,expect,invalid,
    PreservingCompareMachine.parserState,RecordFieldStepMachine.state,
    Function.iterate_succ_apply]

/-- Read just the original pair count and first field; retain the second field
as a raw suffix. This is not validation of the scalar answer or full cache. -/
def decode (word : List Bool) : Option (List Bool × List Bool) := do
  let (n,rest) ← uniformNatRead word
  if n = 2 then FieldPrefixMachine.decode rest else none

def readout (c : Config) : Option (Bool × List Bool) :=
  if c.l = none then c.var.map (fun b => (b,c.stk (.inl (.inl .input)))) else none

private theorem header_read (word : List Bool) (h : word.take 5 = uniformNatEncode 2) :
    uniformNatRead word = some (2,word.drop 5) := by
  have hw : word = uniformNatEncode 2++word.drop 5 := by
    rw [←h]; exact (List.take_append_drop 5 word).symm
  calc uniformNatRead word = uniformNatRead (uniformNatEncode 2++word.drop 5) := congrArg uniformNatRead hw
       _ = some (2,word.drop 5) := uniformNatRead_encode _ _

private theorem decode_bad_header (word : List Bool)
    (h : word.take 5 ≠ uniformNatEncode 2) : decode word = none := by
  unfold decode
  cases hn : uniformNatRead word with
  | none => simp
  | some pair =>
    rcases pair with ⟨n,rest⟩
    by_cases he : n = 2
    · subst n
      have hw := uniformNatRead_exact word 2 rest hn
      have hh : word.take 5 = uniformNatEncode 2 := by
        rw [hw,show uniformNatEncode 2 = [true,true,false,false,true] by decide]
        rfl
      exact (h hh).elim
    · simp [he]

/-- Every raw entry prefix halts. Malformed header/key is none; a valid mismatch
is some(false,suffix). The query and surrounding scan state are preserved. -/
theorem total_run (q word outer archive : List Bool) :
    ∃ fuel ≤ 3*word.length+17+(word.length+1)*(2*word.length+4)+2*q.length,
      let c := tick^[fuel] (start q word outer archive)
      c.l = none ∧ readout c = (decode word).map (fun p => (decide (q = p.1),p.2)) ∧
        c.stk (.inr ()) = q ∧ c.stk (.inl (.inr false)) = outer ∧
        c.stk (.inl (.inr true)) = archive := by
  by_cases hh : word.take 5 = uniformNatEncode 2
  · have hw : word = uniformNatEncode 2++word.drop 5 := by
      rw [←hh]; exact (List.take_append_drop 5 word).symm
    have hd : decode word = FieldPrefixMachine.decode (word.drop 5) := by
      simp [decode,header_read word hh]
    cases hf : FieldPrefixMachine.decode (word.drop 5) with
    | none =>
      obtain ⟨fuel,hb,hl,hv,hq,ho,ha⟩ := rejected_run q (word.drop 5) outer archive hf
      rw [←hw] at hl hv hq ho ha
      have hm := Nat.mul_le_mul
        (show (word.drop 5).length+1 ≤ word.length+1 by simp)
        (show 2*(word.drop 5).length+4 ≤ 2*word.length+4 by simp)
      have hlen : (word.drop 5).length ≤ word.length := by simp
      refine ⟨fuel,by omega,hl,?_,hq,ho,ha⟩
      simp [readout,hl,hv,hd,hf]
    | some pair =>
      rcases pair with ⟨key,suffix⟩
      have hk := fieldDecode_exact (word.drop 5) key suffix hf
      have hw' : word = uniformNatEncode 2++(uniformNatEncode key.length++(key++suffix)) := by
        calc word = uniformNatEncode 2++word.drop 5 := hw
             _ = _ := by rw [hk]
      obtain ⟨fuel,hb,hr⟩ := run q key suffix outer archive
      rw [←hw'] at hr
      have hlen : key.length ≤ word.length := by
        rw [hw']; simp only [List.length_append]; omega
      have hs : key.length.size ≤ word.length :=
        (Nat.size_le.mpr key.length.lt_two_pow_self).trans hlen
      have hm := Nat.mul_le_mul (hlen.trans (Nat.le_succ _))
        (show 2*key.length.size+4 ≤ 2*word.length+4 by omega)
      simp only [Nat.succ_eq_add_one] at hm
      refine ⟨fuel,by omega,?_⟩
      rw [hr]
      simp [readout,state,PreservingCompareMachine.parserState,RecordFieldStepMachine.state,hd,hf]
  · obtain ⟨hl,hv,hq,ho,ha⟩ := header_rejected q word outer archive hh
    refine ⟨5,by omega,hl,?_,hq,ho,ha⟩
    simp only [readout,hl,hv,ite_self,Option.map_none,decode_bad_header word hh]

/-- The input is the actual original encoded cache entry. Execution retains the
query and returns exactly the original scalar-answer frame as its input suffix. -/
theorem entry_run {p q : Nat} [NeZero p] [NeZero q]
    (query key : BallotForkPoint (PrimeGroup p q)) (answer : ZMod q)
    (outer archive : List Bool) :
    ∃ fuel ≤ 3*(keyRecordBitBound p).size+17+
        keyRecordBitBound p*(2*(keyRecordBitBound p).size+4)+2*keyRecordBitBound p,
      tick^[fuel] (start ((ballotKeyBitCodec p q).encode query)
        ((ballotCacheEntryBitCodec p q).encode ⟨key,answer⟩) outer archive) =
      state none ((ballotKeyBitCodec p q).encode query)
        (uniformNatEncode ((primeScalarBitCodec q).encode answer).length++
          (primeScalarBitCodec q).encode answer) [] [] [] outer archive
        (some (decide (query = key))) := by
  have henc : (ballotCacheEntryBitCodec p q).encode ⟨key,answer⟩ =
      uniformNatEncode 2++(uniformNatEncode ((ballotKeyBitCodec p q).encode key).length++
        ((ballotKeyBitCodec p q).encode key++
          (uniformNatEncode ((primeScalarBitCodec q).encode answer).length++
            (primeScalarBitCodec q).encode answer))) := by
    change bitFieldsEncode [_,_] = _
    simp [bitFieldsEncode,bitFramesEncode,List.append_assoc]
  obtain ⟨fuel,hf,hr⟩ := run ((ballotKeyBitCodec p q).encode query)
    ((ballotKeyBitCodec p q).encode key)
    (uniformNatEncode ((primeScalarBitCodec q).encode answer).length++
      (primeScalarBitCodec q).encode answer) outer archive
  have hq := ballotKeyBits_length_le query
  have hk := ballotKeyBits_length_le key
  have hs := Nat.size_le_size hk
  have hm := Nat.mul_le_mul hk (show 2*((ballotKeyBitCodec p q).encode key).length.size+4 ≤
      2*(keyRecordBitBound p).size+4 by omega)
  refine ⟨fuel,by omega,?_⟩
  rw [henc]
  simpa only [(BitRecordCodec.injective (ballotKeyBitCodec p q)).eq_iff] using hr

/-- Matching retains a nonpalindromic answer suffix and both surrounding stacks. -/
theorem match_control :
    ∃ fuel ≤ 43, tick^[fuel] (start [true,false]
      [true,true,false,false,true,true,true,false,false,true,true,false,true,false,true]
      [false,true] [true,false,false]) =
      state none [true,false] [true,false,true] [] [] [] [false,true] [true,false,false] (some true) := by
  exact run [true,false] [true,false] [true,false,true] [false,true] [true,false,false]

/-- A valid unequal key returns some false, retaining the answer suffix. -/
theorem mismatch_control :
    ∃ fuel ≤ 41, tick^[fuel] (start [true]
      [true,true,false,false,true,true,true,false,false,true,true,false,false]
      [] []) = state none [true] [false] [] [] [] [] [] (some false) := by
  exact run [true] [true,false] [false] [] []

/-- A noncanonical key-length prefix returns none, distinct from key mismatch. -/
theorem malformed_control :
    ∃ fuel ≤ 60,
      let c := tick^[fuel]
        (start [true] [true,true,false,false,true,true,false,false] [true] [false])
      c.l = none ∧ c.var = none ∧ c.stk (.inr ()) = [true] ∧
        c.stk (.inl (.inr false)) = [true] ∧ c.stk (.inl (.inr true)) = [false] := by
  exact rejected_run [true] [true,false,false] [true] [false] (by decide)

/-- An empty-record count cannot be accepted as a two-field cache entry. -/
theorem wrong_count_control :
    let c := tick^[5] (start [true,false] [false,false,false,false,false,false] [true] [false])
    c.l = none ∧ c.var = none ∧ c.stk (.inr ()) = [true,false] ∧
      c.stk (.inl (.inr false)) = [true] ∧ c.stk (.inl (.inr true)) = [false] := by
  exact header_rejected _ _ _ _ (by decide)

#print axioms supports
#print axioms header_run
#print axioms run
#print axioms rejected_run
#print axioms header_rejected
#print axioms total_run
#print axioms entry_run
#print axioms match_control
#print axioms mismatch_control
#print axioms malformed_control
#print axioms wrong_count_control
end ExplainableCrypto.Helios.Computational.CacheKeyFieldMachine
