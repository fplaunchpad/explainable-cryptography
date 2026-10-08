import ExplainableCrypto.Helios.Computational.CacheKeyFieldMachine

/-! Complete original entry framing and key comparison. The comparison result
is retained in finite control while answer parsing reuses local memory. -/
namespace ExplainableCrypto.Helios.Computational.CacheEntryMachine
open Turing.TM2
abbrev Stack := CacheKeyFieldMachine.Stack

inductive Label where
  | key (l : CacheKeyFieldMachine.Label)
  | answer (matched : Bool) (l : FieldPrefixMachine.Label)
  | keyDone | answerDone (matched : Bool)
  deriving DecidableEq
open Label
instance : Inhabited Label := ⟨key default⟩
instance : Fintype Label where
  elems := (Finset.univ.image key) ∪ (Finset.univ.image (answer false)) ∪
    (Finset.univ.image (answer true)) ∪ {keyDone,answerDone false,answerDone true}
  complete l := by cases l with
    | key l => simp
    | answer b l => cases b <;> simp
    | keyDone => simp
    | answerDone b => cases b <;> simp
abbrev Config := Cfg (fun _ : Stack => Bool) Label (Option Bool)
private def invalid : Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  .load (fun _ => none) .halt

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | key l => TM2ReturnLink.redirect key keyDone (CacheKeyFieldMachine.program l)
  | answer b l => TM2ReturnLink.redirect (answer b) (answerDone b) (CacheKeyFieldMachine.fieldProgram l)
  | keyDone => .branch Option.isSome
      (.branch (fun x => x.getD false)
        (.load (fun _ => none) (.goto (fun _ => answer true default)))
        (.load (fun _ => none) (.goto (fun _ => answer false default)))) invalid
  | answerDone b => .branch (fun x => decide (x = some true))
      (.peek (.inl (.inl .input)) (fun _ x => x) <| .branch Option.isSome invalid
        (.load (fun _ => some b) .halt)) invalid

def tick (c : Config) : Config := (Turing.TM2.step program c).getD c

def state (phase : Option Label) (q source count temp value outer archive : List Bool)
    (v : Option Bool) : Config :=
  ⟨phase,v,(PreservingCompareMachine.parserState none q source count temp value outer archive v).stk⟩
def start (q word outer archive : List Bool) : Config :=
  TM2ReturnLink.embed key keyDone (CacheKeyFieldMachine.start q word outer archive)

def readout (c : Config) : Option (Bool × List Bool) :=
  if c.l = none then c.var.map (fun b => (b,c.stk (.inl (.inl .output)))) else none

private theorem redirect_supports {L : Type*} (f : L → Label) (ret : Label)
    (s : Stmt (fun _ : Stack => Bool) L (Option Bool)) :
    SupportsStmt Finset.univ (TM2ReturnLink.redirect f ret s) := by
  induction s <;> simp_all [TM2ReturnLink.redirect,SupportsStmt]

theorem supports : Supports program Finset.univ := by
  constructor
  · simp
  · intro l _
    cases l <;> simp [program,invalid,redirect_supports,SupportsStmt]

private theorem key_decode_exact (word key suffix : List Bool)
    (h : CacheKeyFieldMachine.decode word = some (key,suffix)) :
    word = uniformNatEncode 2++(uniformNatEncode key.length++(key++suffix)) := by
  unfold CacheKeyFieldMachine.decode at h
  cases hn : uniformNatRead word with
  | none => simp [hn] at h
  | some pair =>
    rcases pair with ⟨n,rest⟩
    simp only [hn] at h
    dsimp only [Bind.bind,Option.bind] at h
    split at h
    · rename_i he
      subst n
      rw [uniformNatRead_exact word 2 rest hn,fieldDecode_exact rest key suffix h]
    · cases h

/-- Sequential execution specification, proved below equal to the original
strict two-field decoder. Semantic scalar/group validation remains separate. -/
def decode (word : List Bool) : Option (List Bool × List Bool) := do
  let (keyWord,rest) ← CacheKeyFieldMachine.decode word
  let (answerWord,suffix) ← FieldPrefixMachine.decode rest
  if suffix = [] then some (keyWord,answerWord) else none

private theorem decode_encode (key answer : List Bool) :
    decode (bitFieldsEncode [key,answer]) = some (key,answer) := by
  simp [decode,CacheKeyFieldMachine.decode,FieldPrefixMachine.decode,
    bitFieldsEncode,bitFramesEncode,List.append_assoc,uniformNatRead_encode]

private theorem decode_exact (word key answer : List Bool)
    (h : decode word = some (key,answer)) : word = bitFieldsEncode [key,answer] := by
  unfold decode at h
  cases hk : CacheKeyFieldMachine.decode word with
  | none => simp [hk] at h
  | some pair =>
    rcases pair with ⟨k,rest⟩
    simp only [hk] at h
    dsimp only [Bind.bind,Option.bind] at h
    cases ha : FieldPrefixMachine.decode rest with
    | none => simp [ha] at h
    | some pair =>
      rcases pair with ⟨a,suffix⟩
      simp only [ha] at h
      split at h
      · rename_i hs
        subst suffix
        cases Option.some.inj h
        rw [key_decode_exact word _ rest hk,fieldDecode_exact rest _ [] ha]
        simp [bitFieldsEncode,bitFramesEncode,List.append_assoc]
      · cases h

/-- No alternative entry format: the sequential specification exactly matches
count two, two fields and full consumption in the original record decoder. -/
theorem decode_original (word : List Bool) :
    decode word = (bitFieldsDecode word).bind
      (fun | [keyWord,answerWord] => some (keyWord,answerWord) | _ => none) := by
  apply Option.ext
  intro pair
  rcases pair with ⟨key,answer⟩
  constructor
  · intro h
    rw [decode_exact word key answer h,bitFieldsDecode_encode]
    rfl
  · intro h
    cases hc : bitFieldsDecode word with
    | none => simp [hc] at h
    | some fields =>
      rcases fields with (_|⟨k,(_|⟨a,(_|⟨b,tail⟩)⟩)⟩) <;> simp [hc] at h
      rcases h with ⟨rfl,rfl⟩
      rw [bitFieldsDecode_exact _ _ hc]
      exact decode_encode _ _

private theorem answer_enter (b : Bool) (q word outer archive : List Bool) :
    tick (state (some keyDone) q word [] [] [] outer archive (some b)) =
      TM2ReturnLink.embed (answer b) (answerDone b)
        (TM2StackFrame.embed CacheKeyFieldMachine.fieldLayout (FieldPrefixMachine.start word)
          (CacheKeyFieldMachine.fieldFrame q outer archive)) := by
  cases b <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  all_goals
    congr 1
    funext k
    rcases k with ((k|b)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl

private theorem answer_return (b : Bool) (q word outer archive : List Bool) (fuel : Nat)
    (c : FieldPrefixMachine.Config)
    (hr : FieldPrefixMachine.tick^[fuel] (FieldPrefixMachine.start word) = c)
    (hh : c.l = none) :
    ∃ used ≤ fuel, tick^[used]
      (TM2ReturnLink.embed (answer b) (answerDone b)
        (TM2StackFrame.embed CacheKeyFieldMachine.fieldLayout (FieldPrefixMachine.start word)
          (CacheKeyFieldMachine.fieldFrame q outer archive))) =
      TM2ReturnLink.embed (answer b) (answerDone b)
        (TM2StackFrame.embed CacheKeyFieldMachine.fieldLayout c
          (CacheKeyFieldMachine.fieldFrame q outer archive)) := by
  have he := TM2StackFrame.run CacheKeyFieldMachine.fieldLayout FieldPrefixMachine.program fuel
    (FieldPrefixMachine.start word) (CacheKeyFieldMachine.fieldFrame q outer archive)
  change (TM2ReturnLink.tick CacheKeyFieldMachine.fieldProgram)^[fuel] _ =
    TM2StackFrame.embed CacheKeyFieldMachine.fieldLayout (FieldPrefixMachine.tick^[fuel] _) _ at he
  rw [hr] at he
  have hl : ((TM2ReturnLink.tick CacheKeyFieldMachine.fieldProgram)^[fuel]
      (TM2StackFrame.embed CacheKeyFieldMachine.fieldLayout (FieldPrefixMachine.start word)
        (CacheKeyFieldMachine.fieldFrame q outer archive))).l = none := by
    rw [he]; exact hh
  obtain ⟨used,hu,hf⟩ := TM2ReturnLink.run CacheKeyFieldMachine.fieldProgram program
    (answer b) (answerDone b) (fun _ => rfl) _ _ hl
  rw [he] at hf
  exact ⟨used,hu,hf⟩

/-- Parse an answer field and check full consumption, preserving the original
comparison flag in control. Trailing data returns invalid even after a match. -/
theorem answer_run (b : Bool) (q value suffix outer archive : List Bool) :
    ∃ fuel ≤ 3*value.length.size+9+value.length*(2*value.length.size+3),
      tick^[fuel] (state (some keyDone) q
        (uniformNatEncode value.length++(value++suffix)) [] [] [] outer archive (some b)) =
      state none q suffix [] [] value outer archive (if suffix = [] then some b else none) := by
  obtain ⟨j,hj,hr⟩ := RecordFieldStepMachine.field_complete value suffix
  obtain ⟨u,hu,he⟩ := answer_return b q _ outer archive j _ hr rfl
  refine ⟨1+(u+1),by omega,?_⟩
  rw [Function.iterate_add_apply tick 1,Function.iterate_add_apply tick u,
    Function.iterate_one,answer_enter,he]
  cases suffix <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  all_goals
    congr 1
    funext k
    rcases k with ((k|b)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl

private theorem key_run (q k suffix outer archive : List Bool) :
    ∃ fuel ≤ 3*k.length.size+17+k.length*(2*k.length.size+4)+2*q.length,
      tick^[fuel] (start q (uniformNatEncode 2++(uniformNatEncode k.length++(k++suffix))) outer archive) =
      state (some keyDone) q suffix [] [] [] outer archive (some (decide (q = k))) := by
  obtain ⟨j,hj,hr⟩ := CacheKeyFieldMachine.run q k suffix outer archive
  have hh : (CacheKeyFieldMachine.tick^[j]
      (CacheKeyFieldMachine.start q (uniformNatEncode 2++(uniformNatEncode k.length++(k++suffix)))
        outer archive)).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run CacheKeyFieldMachine.program program key keyDone
    (fun _ => rfl) _ _ hh
  change tick^[u] (start q _ outer archive) =
    TM2ReturnLink.embed key keyDone (CacheKeyFieldMachine.tick^[j] _) at he
  rw [hr] at he
  exact ⟨u,hu.trans hj,he⟩

/-- Both framed fields are executed. A trailing suffix invalidates the entry
while query and surrounding scan state remain intact. -/
theorem framed_run (q k value suffix outer archive : List Bool) :
    ∃ fuel ≤ 3*k.length.size+3*value.length.size+26+
        k.length*(2*k.length.size+4)+value.length*(2*value.length.size+3)+2*q.length,
      tick^[fuel] (start q (uniformNatEncode 2++(uniformNatEncode k.length++
        (k++(uniformNatEncode value.length++(value++suffix))))) outer archive) =
      state none q suffix [] [] value outer archive
        (if suffix = [] then some (decide (q = k)) else none) := by
  obtain ⟨u,hu,he⟩ := key_run q k (uniformNatEncode value.length++(value++suffix)) outer archive
  obtain ⟨v,hv,hans⟩ := answer_run (decide (q = k)) q value suffix outer archive
  refine ⟨v+u,by omega,?_⟩
  rw [Function.iterate_add_apply tick v u,he,hans]

/-- Actual complete run on the original encoded two-field record. -/
theorem run (q k value outer archive : List Bool) :
    ∃ fuel ≤ 3*k.length.size+3*value.length.size+26+
        k.length*(2*k.length.size+4)+value.length*(2*value.length.size+3)+2*q.length,
      tick^[fuel] (start q (bitFieldsEncode [k,value]) outer archive) =
      state none q [] [] [] value outer archive (some (decide (q = k))) := by
  simpa [bitFieldsEncode,bitFramesEncode,List.append_assoc] using framed_run q k value [] outer archive

/-- A malformed answer is rejected regardless of the earlier match flag. -/
theorem answer_rejected (b : Bool) (q word outer archive : List Bool)
    (hd : FieldPrefixMachine.decode word = none) :
    ∃ fuel ≤ 3*word.length+7+(word.length+1)*(2*word.length+4),
      let c := tick^[fuel] (state (some keyDone) q word [] [] [] outer archive (some b))
      c.l = none ∧ c.var = none ∧ c.stk (.inr ()) = q ∧
        c.stk (.inl (.inr false)) = outer ∧ c.stk (.inl (.inr true)) = archive := by
  obtain ⟨j,hj,hh,ho⟩ := FieldPrefixMachine.total_run word
  let c := FieldPrefixMachine.tick^[j] (FieldPrefixMachine.start word)
  change c.l = none at hh
  change FieldPrefixMachine.readout c = _ at ho
  have hv : c.var ≠ some true := by
    intro hv
    simp [FieldPrefixMachine.readout,hh,hv,hd] at ho
  obtain ⟨u,hu,he⟩ := answer_return b q word outer archive j c rfl hh
  have hs : tick (TM2ReturnLink.embed (answer b) (answerDone b)
      (TM2StackFrame.embed CacheKeyFieldMachine.fieldLayout c
        (CacheKeyFieldMachine.fieldFrame q outer archive))) =
      ⟨none,none,(TM2StackFrame.embed CacheKeyFieldMachine.fieldLayout c
        (CacheKeyFieldMachine.fieldFrame q outer archive)).stk⟩ := by
    simp [tick,program,invalid,TM2ReturnLink.embed,TM2StackFrame.embed,hh,hv]
  refine ⟨1+(u+1),by omega,?_⟩
  rw [Function.iterate_add_apply tick 1,Function.iterate_add_apply tick u,
    Function.iterate_one,answer_enter,he]
  rw [hs]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

private theorem key_rejected (q word outer archive : List Bool)
    (hd : CacheKeyFieldMachine.decode word = none) :
    ∃ fuel ≤ 3*word.length+18+(word.length+1)*(2*word.length+4)+2*q.length,
      let c := tick^[fuel] (start q word outer archive)
      c.l = none ∧ c.var = none ∧ c.stk (.inr ()) = q ∧
        c.stk (.inl (.inr false)) = outer ∧ c.stk (.inl (.inr true)) = archive := by
  obtain ⟨j,hj,hh,ho,hq,hou,ha⟩ := CacheKeyFieldMachine.total_run q word outer archive
  let c := CacheKeyFieldMachine.tick^[j] (CacheKeyFieldMachine.start q word outer archive)
  change c.l = none at hh
  change CacheKeyFieldMachine.readout c = _ at ho
  have hv : c.var = none := by
    cases hv : c.var with
    | none => rfl
    | some b => simp [CacheKeyFieldMachine.readout,hh,hv,hd] at ho
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run CacheKeyFieldMachine.program program key keyDone
    (fun _ => rfl) _ _ hh
  change tick^[u] (start q word outer archive) = TM2ReturnLink.embed key keyDone c at he
  have hs : tick (TM2ReturnLink.embed key keyDone c) = ⟨none,none,c.stk⟩ := by
    simp [tick,program,invalid,TM2ReturnLink.embed,hh,hv]
  refine ⟨u+1,by omega,?_⟩
  rw [Function.iterate_succ_apply',he,hs]
  exact ⟨rfl,rfl,hq,hou,ha⟩

/-- Every raw entry halts with exact strict two-field framing agreement via
`decode_original`, retaining the query and surrounding scan state. -/
theorem total_run (q word outer archive : List Bool) :
    ∃ fuel ≤ 6*word.length+26+2*(word.length+1)*(2*word.length+4)+2*q.length,
      let c := tick^[fuel] (start q word outer archive)
      c.l = none ∧ readout c = (decode word).map (fun p => (decide (q = p.1),p.2)) ∧
        c.stk (.inr ()) = q ∧ c.stk (.inl (.inr false)) = outer ∧
        c.stk (.inl (.inr true)) = archive := by
  cases hk : CacheKeyFieldMachine.decode word with
  | none =>
    obtain ⟨fuel,hf,hl,hv,hq,ho,ha⟩ := key_rejected q word outer archive hk
    refine ⟨fuel,by simp only [Nat.mul_assoc]; omega,hl,?_,hq,ho,ha⟩
    simp [readout,hl,hv,decode,hk]
  | some pair =>
    rcases pair with ⟨k,rest⟩
    have hw := key_decode_exact word k rest hk
    have hklen : k.length ≤ word.length := by rw [hw]; simp only [List.length_append]; omega
    have hrlen : rest.length ≤ word.length := by rw [hw]; simp only [List.length_append]; omega
    have hks : k.length.size ≤ word.length :=
      (Nat.size_le.mpr k.length.lt_two_pow_self).trans hklen
    have hkm := Nat.mul_le_mul (show k.length ≤ word.length+1 by omega)
      (show 2*k.length.size+4 ≤ 2*word.length+4 by omega)
    cases ha : FieldPrefixMachine.decode rest with
    | none =>
      obtain ⟨u,hu,he⟩ := key_run q k rest outer archive
      rw [←hw] at he
      obtain ⟨v,hv,hl,hflag,hq,ho,har⟩ := answer_rejected (decide (q = k)) q rest outer archive ha
      have hm := Nat.mul_le_mul (Nat.add_le_add_right hrlen 1)
        (show 2*rest.length+4 ≤ 2*word.length+4 by omega)
      refine ⟨v+u,by simp only [Nat.mul_assoc]; omega,?_⟩
      rw [Function.iterate_add_apply tick v u,he]
      refine ⟨hl,?_,hq,ho,har⟩
      simp [readout,hl,hflag,decode,hk,ha]
    | some pair =>
      rcases pair with ⟨a,suffix⟩
      have hr := fieldDecode_exact rest a suffix ha
      have halen : a.length ≤ word.length := by
        have h : a.length ≤ rest.length := by rw [hr]; simp only [List.length_append]; omega
        exact h.trans hrlen
      have has : a.length.size ≤ word.length :=
        (Nat.size_le.mpr a.length.lt_two_pow_self).trans halen
      have ham := Nat.mul_le_mul (show a.length ≤ word.length+1 by omega)
        (show 2*a.length.size+3 ≤ 2*word.length+4 by omega)
      obtain ⟨fuel,hf,he⟩ := framed_run q k a suffix outer archive
      rw [←hr,←hw] at he
      refine ⟨fuel,by simp only [Nat.mul_assoc]; omega,?_⟩
      rw [he]
      by_cases hs : suffix = [] <;>
        simp [readout,state,PreservingCompareMachine.parserState,RecordFieldStepMachine.state,decode,hk,ha,hs]

/-- Complete original typed entry execution, retaining the encoded scalar answer
and deriving the cost from the existing key/scalar codec bounds. -/
theorem entry_run {p q : Nat} [NeZero p] [NeZero q]
    (query k : BallotForkPoint (PrimeGroup p q)) (value : ZMod q) (outer archive : List Bool) :
    ∃ fuel ≤ 3*(keyRecordBitBound p).size+3*(groupRecordBitBound q).size+26+
        keyRecordBitBound p*(2*(keyRecordBitBound p).size+4)+
        groupRecordBitBound q*(2*(groupRecordBitBound q).size+3)+2*keyRecordBitBound p,
      tick^[fuel] (start ((ballotKeyBitCodec p q).encode query)
        ((ballotCacheEntryBitCodec p q).encode ⟨k,value⟩) outer archive) =
      state none ((ballotKeyBitCodec p q).encode query) [] [] []
        ((primeScalarBitCodec q).encode value) outer archive (some (decide (query = k))) := by
  obtain ⟨fuel,hf,hr⟩ := run ((ballotKeyBitCodec p q).encode query)
    ((ballotKeyBitCodec p q).encode k) ((primeScalarBitCodec q).encode value) outer archive
  have hq := ballotKeyBits_length_le query
  have hk := ballotKeyBits_length_le k
  have ha : ((primeScalarBitCodec q).encode value).length ≤ groupRecordBitBound q :=
    scalarEncode_length_le value
  have hks := Nat.size_le_size hk
  have has := Nat.size_le_size ha
  have hkm := Nat.mul_le_mul hk (show 2*((ballotKeyBitCodec p q).encode k).length.size+4 ≤
    2*(keyRecordBitBound p).size+4 by omega)
  have ham := Nat.mul_le_mul ha (show 2*((primeScalarBitCodec q).encode value).length.size+3 ≤
    2*(groupRecordBitBound q).size+3 by omega)
  refine ⟨fuel,by omega,?_⟩
  change tick^[fuel] (start ((ballotKeyBitCodec p q).encode query)
    (bitFieldsEncode [(ballotKeyBitCodec p q).encode k,(primeScalarBitCodec q).encode value])
    outer archive) = _
  simpa only [(BitRecordCodec.injective (ballotKeyBitCodec p q)).eq_iff] using hr

/-- Both fields are consumed; the nonpalindromic answer and all frame data survive. -/
theorem match_control :
    ∃ fuel ≤ 79, tick^[fuel]
      (start [true,false] (bitFieldsEncode [[true,false],[true,false,false]]) [true] [false,true]) =
      state none [true,false] [] [] [] [true,false,false] [true] [false,true] (some true) := by
  exact run [true,false] [true,false] [true,false,false] [true] [false,true]

/-- Answer-parser success must not overwrite an earlier key mismatch. -/
theorem mismatch_control :
    ∃ fuel ≤ 57, tick^[fuel]
      (start [true] (bitFieldsEncode [[false],[true,false]]) [] []) =
      state none [true] [] [] [] [true,false] [] [] (some false) := by
  exact run [true] [false] [true,false] [] []

/-- An explicitly framed empty answer is distinct from a missing answer frame. -/
theorem empty_answer_control :
    ∃ fuel ≤ 26, tick^[fuel] (start [] (bitFieldsEncode [[],[]]) [] []) =
      state none [] [] [] [] [] [] [] (some true) := by
  exact run [] [] [] [] []

/-- Count two followed by only one empty field must actually halt invalid. -/
theorem missing_answer_control :
    ∃ fuel ≤ 300,
      let c := tick^[fuel] (start [] [true,true,false,false,true,false] [true] [false])
      c.l = none ∧ readout c = none ∧ c.stk (.inr ()) = [] ∧
        c.stk (.inl (.inr false)) = [true] ∧ c.stk (.inl (.inr true)) = [false] := by
  obtain ⟨fuel,hf,hh,ho,hq,hou,ha⟩ := total_run [] [true,true,false,false,true,false] [true] [false]
  exact ⟨fuel,hf.trans (by decide),hh,ho,hq,hou,ha⟩

/-- A matching entry with an extra bit rejects and retains the observed suffix. -/
theorem trailing_control :
    ∃ fuel ≤ 26, tick^[fuel] (start [] [true,true,false,false,true,false,false,true] [true] [false]) =
      state none [] [true] [] [] [] [true] [false] none := by
  exact framed_run [] [] [] [true] [true] [false]

#print axioms supports
#print axioms decode_original
#print axioms answer_run
#print axioms run
#print axioms framed_run
#print axioms answer_rejected
#print axioms total_run
#print axioms entry_run
#print axioms match_control
#print axioms mismatch_control
#print axioms empty_answer_control
#print axioms missing_answer_control
#print axioms trailing_control
end ExplainableCrypto.Helios.Computational.CacheEntryMachine
