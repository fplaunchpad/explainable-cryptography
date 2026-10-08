import ExplainableCrypto.Helios.Computational.CacheEntryMachine
import ExplainableCrypto.Helios.Computational.BallotCacheCodecControls

/-! Executed lookup in the original source-generated cache encoding.
Eight binary stacks retain the original cache and query across entry traversal. -/
namespace ExplainableCrypto.Helios.Computational.CacheLookupMachine
open Turing.TM2
abbrev Stack := CacheEntryMachine.Stack ⊕ Unit
abbrev src : Stack := .inl (.inl (.inl .input))
abbrev cnt : Stack := .inl (.inl (.inl .count))
abbrev temp : Stack := .inl (.inl (.inl .scratch))
abbrev out : Stack := .inl (.inl (.inl .output))
abbrev outer : Stack := .inl (.inl (.inr false))
abbrev archive : Stack := .inl (.inl (.inr true))
abbrev query : Stack := .inl (.inr ())
abbrev saved : Stack := .inr ()

inductive Extra where
  | counter | archive | query | cache
  deriving DecidableEq

def fieldLayout : NatPrefixMachine.Stack ⊕ Extra ≃ Stack where
  toFun
    | .inl k => .inl (.inl (.inl k))
    | .inr .counter => outer | .inr .archive => archive
    | .inr .query => query | .inr .cache => saved
  invFun
    | .inl (.inl (.inl k)) => .inl k
    | .inl (.inl (.inr false)) => .inr .counter
    | .inl (.inl (.inr true)) => .inr .archive
    | .inl (.inr _) => .inr .query
    | .inr _ => .inr .cache
  left_inv x := by
    rcases x with (k|e)
    · cases k <;> rfl
    · cases e <;> rfl
  right_inv x := by
    rcases x with (((k|b)|⟨⟩)|⟨⟩)
    · rfl
    · cases b <;> rfl
    · rfl
    · rfl

def countLayout := fieldLayout.trans (Equiv.swap out outer)
def entryLayout : CacheEntryMachine.Stack ⊕ Unit ≃ Stack :=
  (Equiv.swap src out).trans (Equiv.swap src archive)

def fieldFrame (q counter value cache : List Bool) : Extra → List Bool
  | .counter => counter | .archive => value | .query => q | .cache => cache

inductive CopyExtra where
  | count | output | counter | archive | query
  deriving DecidableEq

def copyLayout : BitCopyMachine.Stack ⊕ CopyExtra ≃ Stack where
  toFun
    | .inl .source => src | .inl .destination => saved | .inl .scratch => temp
    | .inr .count => cnt | .inr .output => out | .inr .counter => outer
    | .inr .archive => archive | .inr .query => query
  invFun
    | .inl (.inl (.inl .input)) => .inl .source
    | .inl (.inl (.inl .count)) => .inr .count
    | .inl (.inl (.inl .scratch)) => .inl .scratch
    | .inl (.inl (.inl .output)) => .inr .output
    | .inl (.inl (.inr false)) => .inr .counter
    | .inl (.inl (.inr true)) => .inr .archive
    | .inl (.inr _) => .inr .query
    | .inr _ => .inl .destination
  left_inv x := by
    rcases x with (k|e)
    · cases k <;> rfl
    · cases e <;> rfl
  right_inv x := by
    rcases x with (((k|b)|⟨⟩)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl
    · rfl

def copyFrame (q count output counter value : List Bool) : CopyExtra → List Bool
  | .count => count | .output => output | .counter => counter
  | .archive => value | .query => q

inductive Label where
  | copy (b : Bool) | count (l : NatPrefixMachine.Label)
  | field (l : FieldPrefixMachine.Label) | entry (l : CacheEntryMachine.Label)
  | decrement (b : Bool)
  | copyDone | countDone | loop | fieldDone | entryDone | clear | decDone
  deriving DecidableEq
open Label
instance : Inhabited Label := ⟨copy false⟩
instance : Fintype Label where
  elems := (Finset.univ.image copy) ∪ (Finset.univ.image count) ∪
    (Finset.univ.image field) ∪ (Finset.univ.image entry) ∪ (Finset.univ.image decrement) ∪
    {copyDone,countDone,loop,fieldDone,entryDone,clear,decDone}
  complete l := by cases l <;> simp
abbrev Config := Cfg (fun _ : Stack => Bool) Label (Option Bool)
private def invalid : Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  .load (fun _ => none) .halt

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | copy b => TM2ReturnLink.redirect copy copyDone (TM2StackFrame.relocate copyLayout (BitCopyMachine.program b))
  | count l => TM2ReturnLink.redirect count countDone (TM2StackFrame.relocate countLayout (NatPrefixMachine.program l))
  | field l => TM2ReturnLink.redirect field fieldDone (TM2StackFrame.relocate fieldLayout (FieldPrefixMachine.program l))
  | entry l => TM2ReturnLink.redirect entry entryDone (TM2StackFrame.relocate entryLayout (CacheEntryMachine.program l))
  | decrement b => TM2ReturnLink.redirect decrement decDone
      (TM2StackFrame.relocate countLayout (BitCounterMachine.program b))
  | copyDone => .load (fun _ => none) (.goto (fun _ => count default))
  | countDone | decDone => .branch (fun v => decide (v = some true)) (.goto (fun _ => loop)) invalid
  | loop => .peek outer (fun _ b => b) <| .branch Option.isSome
      (.load (fun _ => none) (.goto (fun _ => field default)))
      (.peek src (fun _ b => b) <| .branch Option.isSome invalid (.load (fun _ => some false) .halt))
  | fieldDone => .branch (fun v => decide (v = some true))
      (.load (fun _ => none) (.goto (fun _ => entry default))) invalid
  | entryDone => .branch Option.isSome
      (.branch (fun v => v.getD false) (.load (fun _ => some true) .halt) (.goto (fun _ => clear))) invalid
  | clear => .pop archive (fun _ b => b) <| .branch Option.isSome
      (.goto (fun _ => clear)) (.load (fun _ => none) (.goto (fun _ => decrement false)))

def tick (c : Config) : Config := (Turing.TM2.step program c).getD c

def state (phase : Option Label) (q source count scratch output counter value cache : List Bool)
    (v : Option Bool) : Config :=
  ⟨phase,v,fun
    | .inl k => (PreservingCompareMachine.parserState none q source count scratch output counter value v).stk k
    | .inr _ => cache⟩
def start (q word : List Bool) : Config := state (some (copy false)) q word [] [] [] [] [] [] none

def readout (c : Config) : Option (Option (List Bool)) :=
  if c.l = none then
    match c.var with
    | none => none | some false => some none | some true => some (some (c.stk archive))
  else none

private theorem redirect_supports {L : Type*} (f : L → Label) (ret : Label)
    (s : Stmt (fun _ : Stack => Bool) L (Option Bool)) :
    SupportsStmt Finset.univ (TM2ReturnLink.redirect f ret s) := by
  induction s <;> simp_all [TM2ReturnLink.redirect,SupportsStmt]

theorem supports : Supports program Finset.univ := by
  constructor
  · simp
  · intro l _
    cases l <;> simp [program,invalid,redirect_supports,SupportsStmt]

private theorem call_run {K E L : Type} [DecidableEq K]
    (layout : K ⊕ E ≃ Stack) (p : L → Stmt (fun _ : K => Bool) L (Option Bool))
    (f : L → Label) (ret : Label)
    (hp : ∀ l, program (f l) = TM2ReturnLink.redirect f ret (TM2StackFrame.relocate layout (p l)))
    (fuel : Nat) (c : Cfg (fun _ : K => Bool) L (Option Bool)) (frame : E → List Bool)
    (hh : ((TM2ReturnLink.tick p)^[fuel] c).l = none) :
    ∃ used ≤ fuel, tick^[used] (TM2ReturnLink.embed f ret (TM2StackFrame.embed layout c frame)) =
      TM2ReturnLink.embed f ret (TM2StackFrame.embed layout ((TM2ReturnLink.tick p)^[fuel] c) frame) := by
  have he := TM2StackFrame.run layout p fuel c frame
  have hl : ((TM2ReturnLink.tick (fun l => TM2StackFrame.relocate layout (p l)))^[fuel]
      (TM2StackFrame.embed layout c frame)).l = none := by
    rw [he]; exact hh
  obtain ⟨used,hu,hr⟩ := TM2ReturnLink.run (fun l => TM2StackFrame.relocate layout (p l))
    program f ret hp _ _ hl
  rw [he] at hr
  exact ⟨used,hu,hr⟩

private theorem field_run (q bytes suffix counter cache : List Bool) :
    ∃ fuel ≤ 3*bytes.length.size+7+bytes.length*(2*bytes.length.size+3),
      tick^[fuel] (state (some (field default)) q
        (uniformNatEncode bytes.length++(bytes++suffix)) [] [] [] counter [] cache none) =
      state (some fieldDone) q suffix [] [] bytes counter [] cache (some true) := by
  obtain ⟨j,hj,hr⟩ := RecordFieldStepMachine.field_complete bytes suffix
  have hh : (FieldPrefixMachine.tick^[j]
      (FieldPrefixMachine.start (uniformNatEncode bytes.length++(bytes++suffix)))).l = none := by rw [hr]
  obtain ⟨u,hu,he⟩ := call_run fieldLayout FieldPrefixMachine.program field fieldDone (fun _ => rfl)
    j (FieldPrefixMachine.start _) (fieldFrame q counter [] cache) hh
  change tick^[u] _ = TM2ReturnLink.embed field fieldDone
    (TM2StackFrame.embed fieldLayout (FieldPrefixMachine.tick^[j] _) _) at he
  rw [hr] at he
  have hs : TM2ReturnLink.embed field fieldDone
      (TM2StackFrame.embed fieldLayout (FieldPrefixMachine.start
        (uniformNatEncode bytes.length++(bytes++suffix))) (fieldFrame q counter [] cache)) =
      state (some (field default)) q (uniformNatEncode bytes.length++(bytes++suffix))
        [] [] [] counter [] cache none := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    rcases k with (((k|b)|⟨⟩)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl
    · rfl
  rw [hs] at he
  refine ⟨u,hu.trans hj,he.trans ?_⟩
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k
  rcases k with (((k|b)|⟨⟩)|⟨⟩)
  · cases k <;> rfl
  · cases b <;> rfl
  · rfl
  · rfl

def entryCost (p q : Nat) : Nat :=
  3*(keyRecordBitBound p).size+3*(groupRecordBitBound q).size+26+
  keyRecordBitBound p*(2*(keyRecordBitBound p).size+4)+
  groupRecordBitBound q*(2*(groupRecordBitBound q).size+3)+2*keyRecordBitBound p

def fieldCost (p q : Nat) : Nat :=
  3*(cacheEntryBitBound p q).size+7+
    cacheEntryBitBound p q*(2*(cacheEntryBitBound p q).size+3)

def iterationCost (p q n : Nat) : Nat :=
  fieldCost p q+entryCost p q+groupRecordBitBound q+2*n.size+6

private theorem iteration_mono {p q a b : Nat} (h : a ≤ b) :
    iterationCost p q a ≤ iterationCost p q b := by
  have hs := Nat.size_le_size h
  unfold iterationCost
  omega

private theorem entry_run {p q : Nat} [NeZero p] [NeZero q]
    (queryKey k : BallotForkPoint (PrimeGroup p q)) (value : ZMod q)
    (suffix counter cache : List Bool) :
    ∃ fuel ≤ entryCost p q,
      tick^[fuel] (state (some (entry default)) ((ballotKeyBitCodec p q).encode queryKey)
        suffix [] [] ((ballotCacheEntryBitCodec p q).encode ⟨k,value⟩) counter [] cache none) =
      state (some entryDone) ((ballotKeyBitCodec p q).encode queryKey) suffix [] [] [] counter
        ((primeScalarBitCodec q).encode value) cache (some (decide (queryKey = k))) := by
  obtain ⟨j,hj,hr⟩ := CacheEntryMachine.entry_run queryKey k value counter suffix
  have hh : (CacheEntryMachine.tick^[j] (CacheEntryMachine.start ((ballotKeyBitCodec p q).encode queryKey)
      ((ballotCacheEntryBitCodec p q).encode ⟨k,value⟩) counter suffix)).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := call_run entryLayout CacheEntryMachine.program entry entryDone (fun _ => rfl)
    j (CacheEntryMachine.start _ _ _ _) (fun _ => cache) hh
  change tick^[u] _ = TM2ReturnLink.embed entry entryDone
    (TM2StackFrame.embed entryLayout (CacheEntryMachine.tick^[j] _) _) at he
  rw [hr] at he
  have hs : TM2ReturnLink.embed entry entryDone (TM2StackFrame.embed entryLayout
      (CacheEntryMachine.start ((ballotKeyBitCodec p q).encode queryKey)
        ((ballotCacheEntryBitCodec p q).encode ⟨k,value⟩) counter suffix) (fun _ => cache)) =
      state (some (entry default)) ((ballotKeyBitCodec p q).encode queryKey) suffix [] []
        ((ballotCacheEntryBitCodec p q).encode ⟨k,value⟩) counter [] cache none := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    rcases k with (((k|b)|⟨⟩)|⟨⟩)
    · cases k <;> simp [TM2StackFrame.embed,TM2StackFrame.data,entryLayout,Equiv.swap_apply_def,
        TM2ReturnLink.embed,CacheEntryMachine.start,CacheKeyFieldMachine.start,CacheKeyFieldMachine.state,
        PreservingCompareMachine.parserState,RecordFieldStepMachine.state]
    · cases b <;> rfl
    · rfl
    · rfl
  rw [hs] at he
  refine ⟨u,hu.trans hj,he.trans ?_⟩
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k
  rcases k with (((k|b)|⟨⟩)|⟨⟩)
  · cases k <;> simp [TM2StackFrame.embed,TM2StackFrame.data,entryLayout,Equiv.swap_apply_def,
      CacheEntryMachine.state,PreservingCompareMachine.parserState,RecordFieldStepMachine.state]
  · cases b <;> rfl
  · rfl
  · rfl

private theorem clear_run (q suffix counter value cache : List Bool) (v : Option Bool) :
    tick^[value.length+1] (state (some clear) q suffix [] [] [] counter value cache v) =
      state (some (decrement false)) q suffix [] [] [] counter [] cache none := by
  induction value generalizing v with
  | nil => simp [tick,state,program,PreservingCompareMachine.parserState,
      RecordFieldStepMachine.state,stepAux]
  | cons b bs ih =>
    have hs : tick (state (some clear) q suffix [] [] [] counter (b::bs) cache v) =
        state (some clear) q suffix [] [] [] counter bs cache (some b) := by
      simp [tick,state,program,PreservingCompareMachine.parserState,
        RecordFieldStepMachine.state,stepAux]
      funext k
      rcases k with (((k|b)|⟨⟩)|⟨⟩)
      · cases k <;> simp
      · cases b <;> simp
      · simp
      · simp
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,hs,ih]

private theorem decrement_run (n : Nat) (q suffix cache : List Bool) :
    ∃ fuel ≤ 2*(n+1).size+2,
      tick^[fuel] (state (some (decrement false)) q suffix [] [] [] (n+1).bits [] cache none) =
        state (some loop) q suffix [] [] [] n.bits [] cache (some true) := by
  obtain ⟨j,hj,hr⟩ := BitCounterMachine.run (n+1) suffix [] none
  simp only [Nat.add_sub_cancel,Nat.add_one_ne_zero,ne_eq,not_false_eq_true,decide_true] at hr
  have hh : (BitCounterMachine.tick^[j]
      (BitCounterMachine.config (some false) (n+1).bits [] suffix [] none)).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := call_run countLayout BitCounterMachine.program decrement decDone (fun _ => rfl)
    j (BitCounterMachine.config (some false) (n+1).bits [] suffix [] none) (fieldFrame q [] [] cache) hh
  change tick^[u] _ = TM2ReturnLink.embed decrement decDone
    (TM2StackFrame.embed countLayout (BitCounterMachine.tick^[j] _) _) at he
  rw [hr] at he
  have hs : TM2ReturnLink.embed decrement decDone (TM2StackFrame.embed countLayout
      (BitCounterMachine.config (some false) (n+1).bits [] suffix [] none) (fieldFrame q [] [] cache)) =
      state (some (decrement false)) q suffix [] [] [] (n+1).bits [] cache none := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    rcases k with (((k|b)|⟨⟩)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl
    · rfl
  have hf : TM2ReturnLink.embed decrement decDone (TM2StackFrame.embed countLayout
      (BitCounterMachine.config none n.bits [] suffix [] (some true)) (fieldFrame q [] [] cache)) =
      state (some decDone) q suffix [] [] [] n.bits [] cache (some true) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    rcases k with (((k|b)|⟨⟩)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl
    · rfl
  rw [hs,hf] at he
  refine ⟨u+1,by omega,?_⟩
  rw [Function.iterate_succ_apply',he]
  rfl

private theorem loop_positive (n : Nat) (q word cache : List Bool) (v : Option Bool) :
    tick (state (some loop) q word [] [] [] (n+1).bits [] cache v) =
      state (some (field default)) q word [] [] [] (n+1).bits [] cache none := by
  have hn : (n+1).bits ≠ [] := by
    intro he
    have hs : (n+1).size = 0 := by rw [←Nat.size_eq_bits_len,he]; rfl
    have := Nat.size_eq_zero.mp hs
    omega
  cases hb : (n+1).bits with
  | nil => exact (hn hb).elim
  | cons b bs => rfl

private theorem prepare_entry {p q : Nat} [NeZero p] [NeZero q]
    (queryKey k : BallotForkPoint (PrimeGroup p q)) (value : ZMod q)
    (n : Nat) (suffix cache : List Bool) (v : Option Bool) :
    ∃ fuel ≤ fieldCost p q+entryCost p q+2,
      tick^[fuel] (state (some loop) ((ballotKeyBitCodec p q).encode queryKey)
        (uniformNatEncode (((ballotCacheEntryBitCodec p q).encode ⟨k,value⟩).length)++
          (((ballotCacheEntryBitCodec p q).encode ⟨k,value⟩)++suffix))
        [] [] [] (n+1).bits [] cache v) =
      state (some entryDone) ((ballotKeyBitCodec p q).encode queryKey) suffix [] [] [] (n+1).bits
        ((primeScalarBitCodec q).encode value) cache (some (decide (queryKey = k))) := by
  obtain ⟨i,hi,hr⟩ := field_run ((ballotKeyBitCodec p q).encode queryKey)
    ((ballotCacheEntryBitCodec p q).encode ⟨k,value⟩) suffix (n+1).bits cache
  obtain ⟨j,hj,he⟩ := entry_run queryKey k value suffix (n+1).bits cache
  have hb := ballotCacheEntryBits_length_le (⟨k,value⟩ : PrimeCacheEntry p q)
  have hs := Nat.size_le_size hb
  have hm := Nat.mul_le_mul hb (show 2*(((ballotCacheEntryBitCodec p q).encode ⟨k,value⟩).length).size+3 ≤
      2*(cacheEntryBitBound p q).size+3 by omega)
  have hib : i ≤ fieldCost p q := by unfold fieldCost; omega
  have enter : tick (state (some fieldDone) ((ballotKeyBitCodec p q).encode queryKey)
      suffix [] [] ((ballotCacheEntryBitCodec p q).encode ⟨k,value⟩) (n+1).bits [] cache (some true)) =
      state (some (entry default)) ((ballotKeyBitCodec p q).encode queryKey)
        suffix [] [] ((ballotCacheEntryBitCodec p q).encode ⟨k,value⟩) (n+1).bits [] cache none := rfl
  refine ⟨j+(1+(i+1)),by omega,?_⟩
  rw [Function.iterate_add_apply tick j,Function.iterate_add_apply tick 1,
    Function.iterate_one,Function.iterate_succ_apply tick i,loop_positive,hr,enter,he]

private theorem hit_step {p q : Nat} [NeZero p] [NeZero q]
    (key : BallotForkPoint (PrimeGroup p q)) (value : ZMod q)
    (n : Nat) (suffix cache : List Bool) (v : Option Bool) :
    ∃ fuel ≤ iterationCost p q (n+1),
      tick^[fuel] (state (some loop) ((ballotKeyBitCodec p q).encode key)
        (uniformNatEncode (((ballotCacheEntryBitCodec p q).encode ⟨key,value⟩).length)++
          (((ballotCacheEntryBitCodec p q).encode ⟨key,value⟩)++suffix))
        [] [] [] (n+1).bits [] cache v) =
      state none ((ballotKeyBitCodec p q).encode key) suffix [] [] [] (n+1).bits
        ((primeScalarBitCodec q).encode value) cache (some true) := by
  obtain ⟨i,hi,hr⟩ := prepare_entry key key value n suffix cache v
  simp only [decide_true] at hr
  refine ⟨i+1,by unfold iterationCost; omega,?_⟩
  rw [Function.iterate_succ_apply',hr]
  rfl

private theorem miss_step {p q : Nat} [NeZero p] [NeZero q]
    (queryKey k : BallotForkPoint (PrimeGroup p q)) (value : ZMod q)
    (h : queryKey ≠ k) (n : Nat) (suffix cache : List Bool) (v : Option Bool) :
    ∃ fuel ≤ iterationCost p q (n+1),
      tick^[fuel] (state (some loop) ((ballotKeyBitCodec p q).encode queryKey)
        (uniformNatEncode (((ballotCacheEntryBitCodec p q).encode ⟨k,value⟩).length)++
          (((ballotCacheEntryBitCodec p q).encode ⟨k,value⟩)++suffix))
        [] [] [] (n+1).bits [] cache v) =
      state (some loop) ((ballotKeyBitCodec p q).encode queryKey) suffix [] [] [] n.bits [] cache (some true) := by
  obtain ⟨i,hi,hr⟩ := prepare_entry queryKey k value n suffix cache v
  simp only [decide_eq_false h] at hr
  obtain ⟨j,hj,he⟩ := decrement_run n ((ballotKeyBitCodec p q).encode queryKey) suffix cache
  have ha : ((primeScalarBitCodec q).encode value).length ≤ groupRecordBitBound q := scalarEncode_length_le value
  have enter : tick (state (some entryDone) ((ballotKeyBitCodec p q).encode queryKey)
      suffix [] [] [] (n+1).bits ((primeScalarBitCodec q).encode value) cache (some false)) =
      state (some clear) ((ballotKeyBitCodec p q).encode queryKey)
        suffix [] [] [] (n+1).bits ((primeScalarBitCodec q).encode value) cache (some false) := rfl
  refine ⟨j+(((primeScalarBitCodec q).encode value).length+1+(i+1)),by unfold iterationCost; omega,?_⟩
  rw [Function.iterate_add_apply tick j,Function.iterate_add_apply,
    Function.iterate_succ_apply' tick i,hr,enter,clear_run,he]

/-- The actual repeated scan implements the original dependent-list lookup.
Every mismatch derives the next workspace; the query and saved cache survive. -/
theorem loop_run {p q : Nat} [NeZero p] [NeZero q]
    (queryKey : BallotForkPoint (PrimeGroup p q)) (entries : List (PrimeCacheEntry p q))
    (cache : List Bool) (v : Option Bool) :
    ∃ fuel ≤ entries.length*iterationCost p q entries.length+1,
      let c := tick^[fuel] (state (some loop) ((ballotKeyBitCodec p q).encode queryKey)
        (bitFramesEncode (entries.map (ballotCacheEntryBitCodec p q).encode))
        [] [] [] entries.length.bits [] cache v)
      c.l = none ∧ readout c = some ((entries.dlookup queryKey).map (primeScalarBitCodec q).encode) ∧
        c.stk query = (ballotKeyBitCodec p q).encode queryKey ∧ c.stk saved = cache := by
  induction entries generalizing v with
  | nil => exact ⟨1,by simp, rfl,rfl,rfl,rfl⟩
  | cons e es ih =>
    rcases e with ⟨k,value⟩
    by_cases h : queryKey = k
    · subst k
      obtain ⟨i,hi,hr⟩ := hit_step queryKey value es.length
        (bitFramesEncode (es.map (ballotCacheEntryBitCodec p q).encode)) cache v
      have hc : iterationCost p q (es.length+1) ≤ (es.length+1)*iterationCost p q (es.length+1) := by
        exact Nat.le_mul_of_pos_left _ (by omega)
      refine ⟨i,by simpa only [List.length_cons] using hi.trans (by omega),?_⟩
      dsimp only
      simp only [List.map_cons,bitFramesEncode,List.append_assoc,List.length_cons,hr,
        List.dlookup_cons_eq]
      exact ⟨rfl,rfl,rfl,rfl⟩
    · obtain ⟨i,hi,hr⟩ := miss_step queryKey k value h es.length
        (bitFramesEncode (es.map (ballotCacheEntryBitCodec p q).encode)) cache v
      obtain ⟨j,hj,hh,ho,hq,hc⟩ := ih (some true)
      have hm := Nat.mul_le_mul_left es.length (iteration_mono (p := p) (q := q)
        (show es.length ≤ es.length+1 by omega))
      refine ⟨j+i,?_,?_⟩
      · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
        omega
      · dsimp only
        simp only [List.map_cons,bitFramesEncode,List.append_assoc,List.length_cons,
          Function.iterate_add_apply tick j i,hr,List.dlookup_cons_ne es ⟨k,value⟩ h]
        exact ⟨hh,ho,hq,hc⟩

private theorem copy_run (q word : List Bool) :
    ∃ fuel ≤ 2*word.length+3,
      tick^[fuel] (start q word) = state (some (count default)) q word [] [] [] [] [] word none := by
  have hr := BitCopyMachine.run word [] none
  simp only [List.append_nil] at hr
  have hh : (BitCopyMachine.tick^[2*word.length+2]
      (BitCopyMachine.config (some false) word [] [] none)).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := call_run copyLayout BitCopyMachine.program copy copyDone (fun _ => rfl)
    (2*word.length+2) (BitCopyMachine.config (some false) word [] [] none) (copyFrame q [] [] [] []) hh
  change tick^[u] _ = TM2ReturnLink.embed copy copyDone
    (TM2StackFrame.embed copyLayout (BitCopyMachine.tick^[2*word.length+2] _) _) at he
  rw [hr] at he
  have hs : TM2ReturnLink.embed copy copyDone (TM2StackFrame.embed copyLayout
      (BitCopyMachine.config (some false) word [] [] none) (copyFrame q [] [] [] [])) = start q word := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    rcases k with (((k|b)|⟨⟩)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl
    · rfl
  have hf : TM2ReturnLink.embed copy copyDone (TM2StackFrame.embed copyLayout
      (BitCopyMachine.config none word word [] none) (copyFrame q [] [] [] [])) =
      state (some copyDone) q word [] [] [] [] [] word none := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    rcases k with (((k|b)|⟨⟩)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl
    · rfl
  rw [hs,hf] at he
  refine ⟨u+1,by omega,?_⟩
  rw [Function.iterate_succ_apply',he]
  rfl

private theorem count_run (n : Nat) (q body cache : List Bool) :
    ∃ fuel ≤ 3*n.size+4,
      tick^[fuel] (state (some (count default)) q (uniformNatEncode n++body) [] [] [] [] [] cache none) =
        state (some loop) q body [] [] [] n.bits [] cache (some true) := by
  have hr := NatPrefixMachine.encoded_run n body
  have hh : (NatPrefixMachine.tick^[3*n.size+3]
      (NatPrefixMachine.start (uniformNatEncode n++body))).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := call_run countLayout NatPrefixMachine.program count countDone (fun _ => rfl)
    (3*n.size+3) (NatPrefixMachine.start (uniformNatEncode n++body)) (fieldFrame q [] [] cache) hh
  change tick^[u] _ = TM2ReturnLink.embed count countDone
    (TM2StackFrame.embed countLayout (NatPrefixMachine.tick^[3*n.size+3] _) _) at he
  rw [hr] at he
  have hs : TM2ReturnLink.embed count countDone (TM2StackFrame.embed countLayout
      (NatPrefixMachine.start (uniformNatEncode n++body)) (fieldFrame q [] [] cache)) =
      state (some (count default)) q (uniformNatEncode n++body) [] [] [] [] [] cache none := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    rcases k with (((k|b)|⟨⟩)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl
    · rfl
  have hf : TM2ReturnLink.embed count countDone (TM2StackFrame.embed countLayout
      (NatPrefixMachine.config none body [] [] n.bits (some true)) (fieldFrame q [] [] cache)) =
      state (some countDone) q body [] [] [] n.bits [] cache (some true) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    rcases k with (((k|b)|⟨⟩)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl
    · rfl
  rw [hs,hf] at he
  refine ⟨u+1,by omega,?_⟩
  rw [Function.iterate_succ_apply',he]
  rfl

/-- Complete lookup from the original typed cache encoding, including its
initial copy and binary count. No caller-supplied frame or size certificate. -/
theorem run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q)) (queryKey : BallotForkPoint (PrimeGroup p q)) :
    ∃ fuel ≤ 2*((ballotCacheBitCodec p q).encode cache).length+3*cache.entries.length.size+
        cache.entries.length*iterationCost p q cache.entries.length+8,
      let c := tick^[fuel] (start ((ballotKeyBitCodec p q).encode queryKey) ((ballotCacheBitCodec p q).encode cache))
      c.l = none ∧ readout c = some ((cache.lookup queryKey).map (primeScalarBitCodec q).encode) ∧
        c.stk query = (ballotKeyBitCodec p q).encode queryKey ∧ c.stk saved = (ballotCacheBitCodec p q).encode cache := by
  obtain ⟨i,hi,hr⟩ := copy_run ((ballotKeyBitCodec p q).encode queryKey) ((ballotCacheBitCodec p q).encode cache)
  obtain ⟨j,hj,he⟩ := count_run cache.entries.length ((ballotKeyBitCodec p q).encode queryKey)
    (bitFramesEncode (cache.entries.map (ballotCacheEntryBitCodec p q).encode)) ((ballotCacheBitCodec p q).encode cache)
  have hw : (ballotCacheBitCodec p q).encode cache = uniformNatEncode cache.entries.length++
      bitFramesEncode (cache.entries.map (ballotCacheEntryBitCodec p q).encode) := by
    change bitFieldsEncode (cache.entries.map (ballotCacheEntryBitCodec p q).encode) = _
    simp only [bitFieldsEncode,List.length_map]
  rw [←hw] at he
  obtain ⟨k,hk,hh,ho,hq,hc⟩ := loop_run queryKey cache.entries ((ballotCacheBitCodec p q).encode cache) (some true)
  refine ⟨k+(j+i),by omega,?_⟩
  dsimp only
  rw [Function.iterate_add_apply tick k,Function.iterate_add_apply tick j,hr,he]
  exact ⟨hh,ho,hq,hc⟩

private theorem hit_loop_run {p q : Nat} [NeZero p] [NeZero q]
    (queryKey : BallotForkPoint (PrimeGroup p q)) (entries : List (PrimeCacheEntry p q))
    (cache : List Bool) (v : Option Bool) (a : ZMod q) (h : entries.dlookup queryKey = some a) :
    ∃ fuel ≤ entries.length*iterationCost p q entries.length+1, ∃ n tail,
      tick^[fuel] (state (some loop) ((ballotKeyBitCodec p q).encode queryKey)
        (bitFramesEncode (entries.map (ballotCacheEntryBitCodec p q).encode))
        [] [] [] entries.length.bits [] cache v) =
      state none ((ballotKeyBitCodec p q).encode queryKey) tail [] [] [] (n+1).bits
        ((primeScalarBitCodec q).encode a) cache (some true) := by
  induction entries generalizing v with
  | nil => cases h
  | cons e es ih =>
    rcases e with ⟨k,value⟩
    by_cases hk : queryKey = k
    · subst k
      simp only [List.dlookup_cons_eq] at h
      cases Option.some.inj h
      obtain ⟨i,hi,hr⟩ := hit_step queryKey a es.length
        (bitFramesEncode (es.map (ballotCacheEntryBitCodec p q).encode)) cache v
      have hc : iterationCost p q (es.length+1) ≤ (es.length+1)*iterationCost p q (es.length+1) :=
        Nat.le_mul_of_pos_left _ (by omega)
      refine ⟨i,by simpa only [List.length_cons] using hi.trans (by omega),es.length,
        bitFramesEncode (es.map (ballotCacheEntryBitCodec p q).encode),?_⟩
      simpa only [List.map_cons,bitFramesEncode,List.append_assoc,List.length_cons] using hr
    · rw [List.dlookup_cons_ne es ⟨k,value⟩ hk] at h
      obtain ⟨i,hi,hr⟩ := miss_step queryKey k value hk es.length
        (bitFramesEncode (es.map (ballotCacheEntryBitCodec p q).encode)) cache v
      obtain ⟨j,hj,n,tail,he⟩ := ih (some true) h
      have hm := Nat.mul_le_mul_left es.length (iteration_mono (p := p) (q := q)
        (show es.length ≤ es.length+1 by omega))
      refine ⟨j+i,?_,n,tail,?_⟩
      · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]; omega
      · simp only [List.map_cons,bitFramesEncode,List.append_assoc,List.length_cons,
          Function.iterate_add_apply tick j i,hr,he]

/-- Reachable hits derive empty parser workspace, while retaining the actual
answer, unread tail, counter, query and complete original cache. -/
theorem hit_run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q)) (key : BallotForkPoint (PrimeGroup p q))
    (a : ZMod q) (h : cache.lookup key = some a) :
    ∃ fuel ≤ 2*((ballotCacheBitCodec p q).encode cache).length+3*cache.entries.length.size+
        cache.entries.length*iterationCost p q cache.entries.length+8, ∃ n tail,
      tick^[fuel] (start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)) =
        state none ((ballotKeyBitCodec p q).encode key) tail [] [] [] (n+1).bits
          ((primeScalarBitCodec q).encode a) ((ballotCacheBitCodec p q).encode cache) (some true) := by
  obtain ⟨i,hi,hr⟩ := copy_run ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)
  obtain ⟨j,hj,he⟩ := count_run cache.entries.length ((ballotKeyBitCodec p q).encode key)
    (bitFramesEncode (cache.entries.map (ballotCacheEntryBitCodec p q).encode)) ((ballotCacheBitCodec p q).encode cache)
  have hw : (ballotCacheBitCodec p q).encode cache = uniformNatEncode cache.entries.length++
      bitFramesEncode (cache.entries.map (ballotCacheEntryBitCodec p q).encode) := by
    change bitFieldsEncode (cache.entries.map (ballotCacheEntryBitCodec p q).encode) = _
    simp only [bitFieldsEncode,List.length_map]
  rw [←hw] at he
  obtain ⟨k,hk,n,tail,hend⟩ := hit_loop_run key cache.entries ((ballotCacheBitCodec p q).encode cache) (some true) a h
  refine ⟨k+(j+i),by omega,n,tail,?_⟩
  rw [Function.iterate_add_apply tick k,Function.iterate_add_apply tick j,hr,he,hend]

private theorem miss_loop_run {p q : Nat} [NeZero p] [NeZero q]
    (queryKey : BallotForkPoint (PrimeGroup p q)) (entries : List (PrimeCacheEntry p q))
    (cache : List Bool) (v : Option Bool) (h : entries.dlookup queryKey = none) :
    ∃ fuel ≤ entries.length*iterationCost p q entries.length+1,
      tick^[fuel] (state (some loop) ((ballotKeyBitCodec p q).encode queryKey)
        (bitFramesEncode (entries.map (ballotCacheEntryBitCodec p q).encode))
        [] [] [] entries.length.bits [] cache v) =
      state none ((ballotKeyBitCodec p q).encode queryKey) [] [] [] [] [] [] cache (some false) := by
  induction entries generalizing v with
  | nil => exact ⟨1,by simp,rfl⟩
  | cons e es ih =>
    rcases e with ⟨k,value⟩
    have hn : queryKey ≠ k := by
      intro he; subst k
      simp only [List.dlookup_cons_eq] at h
      cases h
    rw [List.dlookup_cons_ne es ⟨k,value⟩ hn] at h
    obtain ⟨i,hi,hr⟩ := miss_step queryKey k value hn es.length
      (bitFramesEncode (es.map (ballotCacheEntryBitCodec p q).encode)) cache v
    obtain ⟨j,hj,he⟩ := ih (some true) h
    have hm := Nat.mul_le_mul_left es.length (iteration_mono (p := p) (q := q)
      (show es.length ≤ es.length+1 by omega))
    refine ⟨j+i,?_,?_⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · simp only [List.map_cons,bitFramesEncode,List.append_assoc,List.length_cons,
        Function.iterate_add_apply tick j i,hr,he]

/-- A complete miss derives the empty workspace required by the insertion
successor. The enclosing insertion theorem must derive the miss condition. -/
theorem miss_run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q)) (queryKey : BallotForkPoint (PrimeGroup p q))
    (h : cache.lookup queryKey = none) :
    ∃ fuel ≤ 2*((ballotCacheBitCodec p q).encode cache).length+3*cache.entries.length.size+
        cache.entries.length*iterationCost p q cache.entries.length+8,
      tick^[fuel] (start ((ballotKeyBitCodec p q).encode queryKey) ((ballotCacheBitCodec p q).encode cache)) =
      state none ((ballotKeyBitCodec p q).encode queryKey) [] [] [] [] [] []
        ((ballotCacheBitCodec p q).encode cache) (some false) := by
  obtain ⟨i,hi,hr⟩ := copy_run ((ballotKeyBitCodec p q).encode queryKey) ((ballotCacheBitCodec p q).encode cache)
  obtain ⟨j,hj,he⟩ := count_run cache.entries.length ((ballotKeyBitCodec p q).encode queryKey)
    (bitFramesEncode (cache.entries.map (ballotCacheEntryBitCodec p q).encode)) ((ballotCacheBitCodec p q).encode cache)
  have hw : (ballotCacheBitCodec p q).encode cache = uniformNatEncode cache.entries.length++
      bitFramesEncode (cache.entries.map (ballotCacheEntryBitCodec p q).encode) := by
    change bitFieldsEncode (cache.entries.map (ballotCacheEntryBitCodec p q).encode) = _
    simp only [bitFieldsEncode,List.length_map]
  rw [←hw] at he
  obtain ⟨k,hk,hf⟩ := miss_loop_run queryKey cache.entries ((ballotCacheBitCodec p q).encode cache) (some true) h
  refine ⟨k+(j+i),by omega,?_⟩
  rw [Function.iterate_add_apply tick k,Function.iterate_add_apply tick j,hr,he,hf]

open OracleComp OracleSpec

/-- Supported repaired source executions derive both entry and complete bit
bounds. The same actual machine retains their cache and query while answering. -/
theorem source_cache_run {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2))
    (n : Nat) (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (result : RepairedSubmissionResult (ZMod q) (PrimeGroup p q) ×
      BallotFiniteLoggedState (ZMod q) (PrimeGroup p q))
    (hs : result ∈ support (runBallotFiniteLogged
      (repairedSubmissionPrimeSourceOracle g pk vote attacker) (∅,[])))
    (queryKey : BallotForkPoint (PrimeGroup p q)) :
    ∃ fuel ≤ 2*cacheRecordBitBound p q (n+15)+3*(n+15).size+
        (n+15)*iterationCost p q (n+15)+8,
      let c := tick^[fuel] (start ((ballotKeyBitCodec p q).encode queryKey)
        ((ballotCacheBitCodec p q).encode result.2.1))
      c.l = none ∧ readout c = some ((result.2.1.lookup queryKey).map (primeScalarBitCodec q).encode) ∧
        c.stk query = (ballotKeyBitCodec p q).encode queryKey ∧
        c.stk saved = (ballotCacheBitCodec p q).encode result.2.1 := by
  obtain ⟨fuel,hf,hr⟩ := run result.2.1 queryKey
  have hw := repairedSubmissionPrime_cache_bits_le g pk vote attacker n hb result hs
  have hn := runBallotFiniteLogged_cache_length_le _ (n+15)
    (repairedSubmissionPrimeSource_query_bound g pk vote attacker n hb) (∅,[]) result hs
  simp only [AList.empty_entries,List.length_nil,Nat.zero_add] at hn
  have hsize := Nat.size_le_size hn
  have hm := Nat.mul_le_mul hn (iteration_mono (p := p) (q := q) hn)
  exact ⟨fuel,by omega,hr⟩

private def fixtureBound : Nat :=
  2*((ballotCacheBitCodec 23 11).encode BallotCacheCodecControls.cache).length+
    3*BallotCacheCodecControls.cache.entries.length.size+
    BallotCacheCodecControls.cache.entries.length*iterationCost 23 11 BallotCacheCodecControls.cache.entries.length+8

/-- The independent fixture stores otherKey first. This hit requires a mismatch,
query restoration, scalar clearing, count decrement, and a second entry call. -/
theorem late_hit_control :
    ∃ fuel ≤ fixtureBound,
      let c := tick^[fuel] (start ((ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.key)
        ((ballotCacheBitCodec 23 11).encode BallotCacheCodecControls.cache))
      c.l = none ∧ readout c = some (some ((primeScalarBitCodec 11).encode 3)) ∧
        c.stk query = (ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.key ∧
        c.stk saved = (ballotCacheBitCodec 23 11).encode BallotCacheCodecControls.cache := by
  unfold fixtureBound
  obtain ⟨fuel,hf,hh,ho,hq,hc⟩ := run BallotCacheCodecControls.cache BallotCacheCodecControls.key
  have he : BallotCacheCodecControls.cache.lookup BallotCacheCodecControls.key = some 3 := by decide
  rw [he,Option.map_some] at ho
  refine ⟨fuel,?_,hh,ho,hq,hc⟩
  with_reducible exact hf

theorem early_hit_control :
    ∃ fuel ≤ fixtureBound,
      let c := tick^[fuel] (start ((ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.otherKey)
        ((ballotCacheBitCodec 23 11).encode BallotCacheCodecControls.cache))
      c.l = none ∧ readout c = some (some ((primeScalarBitCodec 11).encode 5)) ∧
        c.stk query = (ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.otherKey ∧
        c.stk saved = (ballotCacheBitCodec 23 11).encode BallotCacheCodecControls.cache := by
  unfold fixtureBound
  obtain ⟨fuel,hf,hh,ho,hq,hc⟩ := run BallotCacheCodecControls.cache BallotCacheCodecControls.otherKey
  have he : BallotCacheCodecControls.cache.lookup BallotCacheCodecControls.otherKey = some 5 := by decide
  rw [he,Option.map_some] at ho
  refine ⟨fuel,?_,hh,ho,hq,hc⟩
  with_reducible exact hf

private def absentKey : BallotForkPoint (PrimeGroup 23 11) :=
  ({BallotCacheCodecControls.key.1 with generator := BallotCacheCodecControls.key.1.ciphertext.1},
    BallotCacheCodecControls.key.2)

theorem miss_control :
    ∃ fuel ≤ fixtureBound,
      let c := tick^[fuel] (start ((ballotKeyBitCodec 23 11).encode absentKey)
        ((ballotCacheBitCodec 23 11).encode BallotCacheCodecControls.cache))
      c.l = none ∧ readout c = some none ∧
        c.stk query = (ballotKeyBitCodec 23 11).encode absentKey ∧
        c.stk saved = (ballotCacheBitCodec 23 11).encode BallotCacheCodecControls.cache := by
  unfold fixtureBound
  obtain ⟨fuel,hf,hh,ho,hq,hc⟩ := run BallotCacheCodecControls.cache absentKey
  have he : BallotCacheCodecControls.cache.lookup absentKey = none := by decide
  rw [he,Option.map_none] at ho
  refine ⟨fuel,?_,hh,ho,hq,hc⟩
  with_reducible exact hf

theorem empty_control :
    ∃ fuel ≤ 10,
      let c := tick^[fuel] (start ((ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.key) [false])
      c.l = none ∧ readout c = some none ∧
        c.stk query = (ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.key ∧ c.stk saved = [false] := by
  exact run (∅ : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11)) BallotCacheCodecControls.key

/-- Actual rejection distinguishes malformed framing from a successful miss. -/
theorem malformed_controls :
    ∀ word ∈ [[false,true], [true,false,true], [true,false,true,true,false,true,false],
      [true,false,true,true,true,true,false,false,true,true,true,true,false,false,true,false]],
      let c := tick^[200] (start [true] word)
      c.l = none ∧ readout c = none ∧ c.stk query = [true] ∧ c.stk saved = word := by
  decide +kernel

#print axioms supports
#print axioms loop_run
#print axioms run
#print axioms hit_run
#print axioms miss_run
#print axioms source_cache_run
#print axioms late_hit_control
#print axioms early_hit_control
#print axioms miss_control
#print axioms empty_control
#print axioms malformed_controls
end ExplainableCrypto.Helios.Computational.CacheLookupMachine
