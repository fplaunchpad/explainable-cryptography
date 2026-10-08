import ExplainableCrypto.Helios.Computational.RecordFrameFormat

/-! The original counted record, validated and retained by one six-stack TM2.
All counts remain binary; field iteration consumes input and clears workspace. -/
namespace ExplainableCrypto.Helios.Computational.RecordParserMachine
open Turing.TM2
abbrev Stack := RecordFieldStepMachine.Stack

def plainCount (l : NatPrefixMachine.Label) :=
  TM2StackFrame.relocate RecordFieldStepMachine.counterLayout (NatPrefixMachine.program l)
def countProgram (l : NatPrefixMachine.Label) := TM2InputArchive.record (plainCount l)
def countStart (word : List Bool) := TM2InputArchive.withArchive
  (TM2StackFrame.embed RecordFieldStepMachine.counterLayout (NatPrefixMachine.start word)
    (RecordFieldStepMachine.frame [] [])) []

theorem count_eligible : ∀ l, TM2InputArchive.Eligible (plainCount l) := by
  intro l
  cases l <;> simp [plainCount,RecordFieldStepMachine.counterLayout,TM2StackFrame.relocate,
    NatPrefixMachine.program,TM2InputArchive.Eligible,Equiv.swap_apply_def,
    TM2InputArchive.src,TM2InputArchive.dst]
  all_goals exact True.intro

inductive Label where
  | count (phase : NatPrefixMachine.Label) | body (phase : ArchivedFieldMachine.Label)
  | enter | loop | resume | restore
  deriving DecidableEq
open Label
instance : Inhabited Label := ⟨count .width⟩
instance : Fintype Label where
  elems := (Finset.univ.image count) ∪ (Finset.univ.image body) ∪ {enter,loop,resume,restore}
  complete l := by cases l <;> simp

abbrev Config := Cfg (fun _ : Stack => Bool) Label (Option Bool)
private def fail : Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  .load (fun _ => some false) .halt

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .count l => TM2ReturnLink.redirect count enter (countProgram l)
  | .body l => TM2ReturnLink.redirect body resume (ArchivedFieldMachine.program l)
  | enter | resume => .branch (fun v => decide (v = some true)) (.goto (fun _ => loop)) fail
  | loop => .peek (.inr false) (fun _ b => b) <| .branch Option.isSome
      (.load (fun _ => none) (.goto (fun _ => body default)))
      (.peek (.inl .input) (fun _ b => b) <| .branch Option.isSome fail (.goto (fun _ => restore)))
  | restore => .pop (.inr true) (fun _ b => b) <| .branch Option.isSome
      (.push (.inl .output) (fun b => b.getD false) (.goto (fun _ => restore)))
      (.load (fun _ => some true) .halt)

def tick (c : Config) : Config := (Turing.TM2.step program c).getD c

def state (phase : Option Label) (source collected temp value outer archive : List Bool)
    (v : Option Bool) : Config :=
  ⟨phase,v,(RecordFieldStepMachine.state none source collected temp value outer archive v).stk⟩
def start (word : List Bool) : Config := TM2ReturnLink.embed count enter (countStart word)
def readout (c : Config) : Option (List Bool) :=
  if c.l = none ∧ c.var = some true then some (c.stk (.inl .output)) else none

private theorem redirect_supports {L : Type*} (f : L → Label) (ret : Label)
    (s : Stmt (fun _ : Stack => Bool) L (Option Bool)) :
    SupportsStmt Finset.univ (TM2ReturnLink.redirect f ret s) := by
  induction s <;> simp_all [TM2ReturnLink.redirect,SupportsStmt]

theorem supports : Supports program Finset.univ := by
  constructor
  · simp
  · intro l _
    cases l <;> simp [program,fail,redirect_supports,SupportsStmt]

private theorem nonempty_bits {n : Nat} (h : n ≠ 0) : n.bits ≠ [] := by
  intro he
  have hs : n.size = 0 := by rw [←Nat.size_eq_bits_len,he]; rfl
  exact h (Nat.size_eq_zero.mp hs)

private theorem loop_positive (n : Nat) (hn : n ≠ 0) (word archive : List Bool) (v : Option Bool) :
    tick (state (some loop) word [] [] [] n.bits archive v) =
      TM2ReturnLink.embed body resume (ArchivedFieldMachine.start word n.bits archive) := by
  cases hb : n.bits with
  | nil => exact (nonempty_bits hn hb).elim
  | cons b bs =>
    simp [tick,state,program,RecordFieldStepMachine.state]
    congr 1
    funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr b => cases b <;> rfl

/-- One actual positive-count loop step returns to this same loop with a
smaller binary count, a shorter input and its original field frame archived. -/
theorem body_run (bs rest archive : List Bool) (n : Nat) (v : Option Bool) :
    ∃ fuel ≤ 3*bs.length.size+14+bs.length*(2*bs.length.size+4)+2*(n+1).size,
      tick^[fuel] (state (some loop) (uniformNatEncode bs.length ++ (bs++rest)) [] [] [] (n+1).bits archive v) =
        state (some loop) rest [] [] [] n.bits
          ((uniformNatEncode bs.length++bs).reverse++archive) (some true) := by
  obtain ⟨j,hj,he⟩ := ArchivedFieldMachine.run bs rest archive n
  have hh : (ArchivedFieldMachine.tick^[j]
      (ArchivedFieldMachine.start (uniformNatEncode bs.length ++ (bs++rest)) (n+1).bits archive)).l = none := by
    rw [he]; rfl
  obtain ⟨k,hk,hr⟩ := TM2ReturnLink.run ArchivedFieldMachine.program program body resume
    (fun _ => rfl) _ _ hh
  change tick^[k] _ = TM2ReturnLink.embed body resume (ArchivedFieldMachine.tick^[j] _) at hr
  rw [he] at hr
  change tick^[k] _ = state (some resume) rest [] [] [] n.bits
    ((uniformNatEncode bs.length++bs).reverse++archive) (some true) at hr
  refine ⟨1+(k+1),by omega,?_⟩
  rw [Function.iterate_add_apply tick 1 (k+1),Function.iterate_succ_apply tick k,
    loop_positive _ (by omega),hr]
  rfl

/-- Bad fields halt within this loop without a count-dependent search. -/
theorem body_rejected (word archive : List Bool) (n : Nat) (v : Option Bool)
    (h : FieldPrefixMachine.decode word = none) :
    ∃ fuel ≤ 3*word.length+9+(word.length+1)*(2*word.length+4),
      let c := tick^[fuel] (state (some loop) word [] [] [] (n+1).bits archive v)
      c.l = none ∧ c.var = some false := by
  obtain ⟨j,hj,hh,hv,_,_⟩ := ArchivedFieldMachine.rejected_run word (n+1).bits archive h
  let c := ArchivedFieldMachine.tick^[j] (ArchivedFieldMachine.start word (n+1).bits archive)
  change c.l = none at hh
  change c.var ≠ some true at hv
  obtain ⟨k,hk,he⟩ := TM2ReturnLink.run ArchivedFieldMachine.program program body resume
    (fun _ => rfl) _ _ hh
  change tick^[k] _ = TM2ReturnLink.embed body resume c at he
  have hs : tick (TM2ReturnLink.embed body resume c) = ⟨none,some false,c.stk⟩ := by
    simp [tick,TM2ReturnLink.embed,hh,program,fail,stepAux,hv]
  refine ⟨1+(k+1),by omega,?_⟩
  rw [Function.iterate_add_apply tick 1 (k+1),Function.iterate_succ_apply tick k,
    loop_positive _ (by omega),he]
  change (tick _).l = none ∧ (tick _).var = some false
  rw [hs]
  exact ⟨rfl,rfl⟩

private theorem restore_run (archive value : List Bool) (v : Option Bool) :
    tick^[archive.length+1] (state (some restore) [] [] [] value [] archive v) =
      state none [] [] [] (archive.reverse++value) [] [] (some true) := by
  induction archive generalizing value v with
  | nil => simp [tick,state,program,RecordFieldStepMachine.state,stepAux]
  | cons b bs ih =>
    have hs : tick (state (some restore) [] [] [] value [] (b::bs) v) =
        state (some restore) [] [] [] (b::value) [] bs (some b) := by
      simp [tick,state,program,RecordFieldStepMachine.state,stepAux]
      funext k
      cases k with
      | inl k => cases k <;> simp
      | inr b => cases b <;> simp
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,hs,ih]
    simp

/-- A deliberately loose monotone polynomial dominates one field call or
rejection and final restoration. B bounds retained plus remaining input. -/
def unitCost (B width : Nat) : Nat := 3*B+16+(B+1)*(2*B+4)+2*width

private theorem cost_mono {B C n m : Nat} (hB : B ≤ C) (hn : n ≤ m) :
    unitCost B n ≤ unitCost C m := by
  have hm := Nat.mul_le_mul (show B+1 ≤ C+1 by omega) (show 2*B+4 ≤ 2*C+4 by omega)
  unfold unitCost
  omega


/-- The complete repeated field loop agrees with the original recursive reader.
The numeric count may be huge: the bound uses remaining input and bit width. -/
theorem loop_run (n : Nat) (word archive : List Bool) (v : Option Bool) :
    ∃ fuel ≤ (word.length+1)*unitCost (word.length+archive.length) n.size,
      let c := tick^[fuel] (state (some loop) word [] [] [] n.bits archive v)
      c.l = none ∧ readout c = recordBodyResult n word archive := by
  induction n generalizing word archive v with
  | zero =>
    cases word with
    | nil =>
      have hs : tick (state (some loop) [] [] [] [] [] archive v) =
          state (some restore) [] [] [] [] [] archive none := rfl
      have he : tick^[archive.length+2] (state (some loop) [] [] [] [] [] archive v) =
          state none [] [] [] archive.reverse [] [] (some true) := by
        rw [Function.iterate_succ_apply,hs]
        simpa using restore_run archive [] none
      refine ⟨archive.length+2,?_,?_⟩
      · simp only [List.length_nil,Nat.zero_add,Nat.size_zero,Nat.one_mul]
        unfold unitCost
        omega
      · change (tick^[archive.length+2] _).l = none ∧ _
        rw [Nat.zero_bits,he]
        simp [readout,state,RecordFieldStepMachine.state,recordBodyResult_zero]
    | cons b bs =>
      refine ⟨1,?_,?_⟩
      · unfold unitCost
        have hprod := Nat.mul_le_mul_right
          (3*((b::bs).length+archive.length)+16+
            ((b::bs).length+archive.length+1)*(2*((b::bs).length+archive.length)+4)+2*(0:Nat).size)
          (show 1 ≤ (b::bs).length+1 by simp)
        simp only [Nat.one_mul] at hprod
        omega
      · simp [tick,state,program,fail,RecordFieldStepMachine.state,readout,recordBodyResult_zero]
  | succ n ih =>
    cases hd : FieldPrefixMachine.decode word with
    | none =>
      obtain ⟨k,hk,hh,hv⟩ := body_rejected word archive n v hd
      have hm := Nat.mul_le_mul
        (show word.length+1 ≤ word.length+archive.length+1 by omega)
        (show 2*word.length+4 ≤ 2*(word.length+archive.length)+4 by omega)
      have hc : k ≤ unitCost (word.length+archive.length) (n+1).size := by
        unfold unitCost
        omega
      have ht := Nat.mul_le_mul_right (unitCost (word.length+archive.length) (n+1).size)
        (show 1 ≤ word.length+1 by omega)
      simp only [Nat.one_mul] at ht
      refine ⟨k,hc.trans ht,hh,?_⟩
      rw [recordBodyResult_reject n word archive hd]
      simp [readout,hv]
    | some pair =>
      rcases pair with ⟨bs,rest⟩
      have hw := fieldDecode_exact word bs rest hd
      have hlen : 2*bs.length.size+1+bs.length+rest.length = word.length := by
        simp only [hw,List.length_append,uniformNatEncode_length]
        omega
      let archive' := (uniformNatEncode bs.length++bs).reverse++archive
      have hB : rest.length+archive'.length = word.length+archive.length := by
        simp only [archive',List.length_append,List.length_reverse,uniformNatEncode_length]
        omega
      obtain ⟨k,hk,he⟩ := body_run bs rest archive n v
      rw [←hw] at he
      obtain ⟨j,hj,hh,ho⟩ := ih rest archive' (some true)
      rw [hB] at hj
      let A := unitCost (word.length+archive.length) (n+1).size
      have hsize : bs.length.size ≤ word.length+archive.length := by
        have hs := Nat.size_le.mpr bs.length.lt_two_pow_self
        omega
      have hc : k ≤ A := by
        have hm := Nat.mul_le_mul (show bs.length ≤ word.length+archive.length+1 by omega)
          (show 2*bs.length.size+4 ≤ 2*(word.length+archive.length)+4 by omega)
        dsimp [A,unitCost]
        omega
      have hj' : j ≤ (rest.length+1)*A := by
        exact hj.trans (Nat.mul_le_mul_left _ (cost_mono (Nat.le_refl _)
          (Nat.size_le_size (Nat.le_succ n))))
      have ht := Nat.mul_le_mul_right A (show rest.length+2 ≤ word.length+1 by omega)
      refine ⟨j+k,?_,?_⟩
      · change j+k ≤ (word.length+1)*A
        simp only [Nat.add_mul,Nat.one_mul] at hj' ht ⊢
        omega
      · rw [Function.iterate_add_apply tick j k,he]
        refine ⟨hh,?_⟩
        rw [recordBodyResult_next n word bs rest archive hd]
        exact ho


private theorem count_input (c : NatPrefixMachine.Config) :
    (TM2StackFrame.embed RecordFieldStepMachine.counterLayout c
      (RecordFieldStepMachine.frame [] [])).stk TM2InputArchive.src = c.stk .input := by
  simp [TM2StackFrame.embed,TM2StackFrame.data,RecordFieldStepMachine.counterLayout,
    Equiv.swap_apply_def,TM2InputArchive.src]

private theorem count_correspondence (fuel : Nat) (word : List Bool) :
    ∃ consumed, word = consumed ++
        (NatPrefixMachine.tick^[fuel] (NatPrefixMachine.start word)).stk .input ∧
      (TM2ReturnLink.tick countProgram)^[fuel] (countStart word) =
        TM2InputArchive.withArchive
          (TM2StackFrame.embed RecordFieldStepMachine.counterLayout
            (NatPrefixMachine.tick^[fuel] (NatPrefixMachine.start word))
            (RecordFieldStepMachine.frame [] [])) consumed.reverse := by
  have hf := TM2StackFrame.run RecordFieldStepMachine.counterLayout NatPrefixMachine.program fuel
    (NatPrefixMachine.start word) (RecordFieldStepMachine.frame [] [])
  change (TM2ReturnLink.tick plainCount)^[fuel] _ =
    TM2StackFrame.embed RecordFieldStepMachine.counterLayout (NatPrefixMachine.tick^[fuel] _) _ at hf
  obtain ⟨bs,hb,he⟩ := TM2InputArchive.run plainCount count_eligible fuel
    (TM2StackFrame.embed RecordFieldStepMachine.counterLayout (NatPrefixMachine.start word)
      (RecordFieldStepMachine.frame [] [])) []
  rw [hf,count_input,count_input] at hb
  rw [hf,List.append_nil] at he
  exact ⟨bs,hb,he⟩

/-- The original count prefix is executed into the outer binary stack and
archived before entering the repeated loop, with no external invariant premise. -/
theorem count_run (n : Nat) (rest : List Bool) :
    ∃ fuel ≤ 3*n.size+4,
      tick^[fuel] (start (uniformNatEncode n++rest)) =
        state (some loop) rest [] [] [] n.bits (uniformNatEncode n).reverse (some true) := by
  obtain ⟨consumed,hc,hr⟩ := count_correspondence (3*n.size+3) (uniformNatEncode n++rest)
  rw [NatPrefixMachine.encoded_run] at hc hr
  change uniformNatEncode n++rest = consumed++rest at hc
  have hcons : consumed = uniformNatEncode n := (List.append_cancel_right hc).symm
  rw [hcons] at hr
  have hh : ((TM2ReturnLink.tick countProgram)^[3*n.size+3]
      (countStart (uniformNatEncode n++rest))).l = none := by
    rw [hr]; rfl
  obtain ⟨k,hk,he⟩ := TM2ReturnLink.run countProgram program count enter (fun _ => rfl) _ _ hh
  rw [hr] at he
  have hend : TM2ReturnLink.embed count enter
      (TM2InputArchive.withArchive (TM2StackFrame.embed RecordFieldStepMachine.counterLayout
        (NatPrefixMachine.config none rest [] [] n.bits (some true))
        (RecordFieldStepMachine.frame [] [])) (uniformNatEncode n).reverse) =
        state (some enter) rest [] [] [] n.bits (uniformNatEncode n).reverse (some true) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    funext k
    cases k with
    | inl k => cases k <;> simp [TM2InputArchive.withArchive,TM2StackFrame.embed,TM2StackFrame.data,
        RecordFieldStepMachine.counterLayout,Equiv.swap_apply_def,NatPrefixMachine.config,
        RecordFieldStepMachine.frame,TM2InputArchive.dst,RecordFieldStepMachine.state]
    | inr b => cases b <;> simp [TM2InputArchive.withArchive,TM2StackFrame.embed,TM2StackFrame.data,
        RecordFieldStepMachine.counterLayout,NatPrefixMachine.config,
        TM2InputArchive.dst,RecordFieldStepMachine.state]
  rw [hend] at he
  change tick^[k] (start _) = _ at he
  refine ⟨k+1,by omega,?_⟩
  rw [Function.iterate_succ_apply',he]
  rfl

/-- A malformed outer count halts before entering the field loop. -/
theorem count_rejected (word : List Bool) (h : uniformNatRead word = none) :
    ∃ fuel ≤ 3*word.length+4,
      let c := tick^[fuel] (start word)
      c.l = none ∧ c.var = some false := by
  obtain ⟨j,hj,hh,ho⟩ := NatPrefixMachine.total_run word
  let c := NatPrefixMachine.tick^[j] (NatPrefixMachine.start word)
  change c.l = none at hh
  change NatPrefixMachine.readout c = _ at ho
  have hv : c.var ≠ some true := by
    intro hv
    simp [NatPrefixMachine.readout,hh,hv,h] at ho
  obtain ⟨consumed,_,hr⟩ := count_correspondence j word
  change (TM2ReturnLink.tick countProgram)^[j] (countStart word) =
    TM2InputArchive.withArchive (TM2StackFrame.embed RecordFieldStepMachine.counterLayout c
      (RecordFieldStepMachine.frame [] [])) consumed.reverse at hr
  have hhalt : ((TM2ReturnLink.tick countProgram)^[j] (countStart word)).l = none := by
    rw [hr]; exact hh
  obtain ⟨k,hk,he⟩ := TM2ReturnLink.run countProgram program count enter (fun _ => rfl) _ _ hhalt
  rw [hr] at he
  change tick^[k] (start word) = _ at he
  have hs : tick (TM2ReturnLink.embed count enter
      (TM2InputArchive.withArchive (TM2StackFrame.embed RecordFieldStepMachine.counterLayout c
        (RecordFieldStepMachine.frame [] [])) consumed.reverse)) =
      ⟨none,some false,(TM2InputArchive.withArchive
        (TM2StackFrame.embed RecordFieldStepMachine.counterLayout c
          (RecordFieldStepMachine.frame [] [])) consumed.reverse).stk⟩ := by
    simp [tick,TM2ReturnLink.embed,TM2InputArchive.withArchive,TM2StackFrame.embed,hh,program,fail,stepAux,hv]
  refine ⟨k+1,by omega,?_⟩
  change (tick^[k+1] _).l = none ∧ _
  rw [Function.iterate_succ_apply',he,hs]
  exact ⟨rfl,rfl⟩

/-- Every raw record halts with exact agreement with the original decoder.
Accepted output is the entire original encoded record, including its count. -/
theorem total_run (word : List Bool) :
    ∃ fuel ≤ 3*word.length+4+(word.length+1)*unitCost word.length word.length,
      let c := tick^[fuel] (start word)
      c.l = none ∧ readout c = (bitFieldsDecode word).map (fun _ => word) := by
  cases h : uniformNatRead word with
  | none =>
    obtain ⟨k,hk,hh,hv⟩ := count_rejected word h
    refine ⟨k,by omega,hh,?_⟩
    simp [readout,hv,bitFieldsDecode,h]
  | some pair =>
    rcases pair with ⟨n,rest⟩
    obtain ⟨k,hk,hc⟩ := count_run n rest
    have hw := uniformNatRead_exact word n rest h
    rw [←hw] at hc
    obtain ⟨j,hj,hh,ho⟩ := loop_run n rest (uniformNatEncode n).reverse (some true)
    have hlen : 2*n.size+1+rest.length = word.length := by
      rw [hw,List.length_append,uniformNatEncode_length]
    have hb : rest.length+(uniformNatEncode n).reverse.length = word.length := by
      rw [List.length_reverse,uniformNatEncode_length]
      omega
    rw [hb] at hj
    have hs : n.size ≤ word.length := by omega
    have hm := Nat.mul_le_mul (show rest.length+1 ≤ word.length+1 by omega)
      (cost_mono (Nat.le_refl word.length) hs)
    refine ⟨j+k,by omega,?_⟩
    rw [Function.iterate_add_apply tick j k,hc]
    exact ⟨hh,ho.trans (recordBodyResult_original word n rest h)⟩

private theorem bounded_run (word : List Bool) (B : Nat) (hb : word.length ≤ B) :
    ∃ fuel ≤ 3*B+4+(B+1)*unitCost B B,
      let c := tick^[fuel] (start word)
      c.l = none ∧ readout c = (bitFieldsDecode word).map (fun _ => word) := by
  obtain ⟨fuel,hf,hh,ho⟩ := total_run word
  have hm := Nat.mul_le_mul (Nat.add_le_add_right hb 1) (cost_mono hb hb)
  exact ⟨fuel,by omega,hh,ho⟩

/-- Validate the original framing of an encoded cache. This checks counted
fields; group membership and duplicate-key validation are separate operations. -/
theorem cache_run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q)) :
    ∃ fuel ≤ 3*cacheRecordBitBound p q cache.entries.length+4+
        (cacheRecordBitBound p q cache.entries.length+1)*
          unitCost (cacheRecordBitBound p q cache.entries.length)
            (cacheRecordBitBound p q cache.entries.length),
      let c := tick^[fuel] (start ((ballotCacheBitCodec p q).encode cache))
      c.l = none ∧ readout c = some ((ballotCacheBitCodec p q).encode cache) := by
  obtain ⟨fuel,hf,hh,ho⟩ := bounded_run _ _ (ballotCacheBits_length_le cache)
  refine ⟨fuel,hf,hh,?_⟩
  change readout _ = (bitFieldsDecode (bitFieldsEncode
    (cache.entries.map (ballotCacheEntryBitCodec p q).encode))).map _ at ho
  simpa only [bitFieldsDecode_encode,Option.map_some] using ho

open OracleComp OracleSpec

/-- Actual explicit-source results supply the cache framing bound through their
own hash-query budget. No cache-size or machine-cost certificate is assumed. -/
theorem source_cache_run {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2))
    (n : Nat) (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (out : RepairedSubmissionResult (ZMod q) (PrimeGroup p q) ×
      BallotFiniteLoggedState (ZMod q) (PrimeGroup p q))
    (ho : out ∈ support (runBallotFiniteLogged
      (repairedSubmissionPrimeSourceOracle g pk vote attacker) (∅,[]))) :
    ∃ fuel ≤ 3*cacheRecordBitBound p q (n+15)+4+
        (cacheRecordBitBound p q (n+15)+1)*
          unitCost (cacheRecordBitBound p q (n+15)) (cacheRecordBitBound p q (n+15)),
      let c := tick^[fuel] (start ((ballotCacheBitCodec p q).encode out.2.1))
      c.l = none ∧ readout c = some ((ballotCacheBitCodec p q).encode out.2.1) := by
  obtain ⟨fuel,hf,hh,hr⟩ := bounded_run _ _
    (repairedSubmissionPrime_cache_bits_le g pk vote attacker n hb out ho)
  refine ⟨fuel,hf,hh,?_⟩
  change readout _ = (bitFieldsDecode (bitFieldsEncode
    (out.2.1.entries.map (ballotCacheEntryBitCodec p q).encode))).map _ at hr
  simpa only [bitFieldsDecode_encode,Option.map_some] using hr

/-- The empty record retains its one-bit count header in successful output. -/
theorem empty_record_control :
    ∃ fuel ≤ 100, let c := tick^[fuel] (start [false])
      c.l = none ∧ readout c = some [false] := by
  obtain ⟨fuel,hf,hh,ho⟩ := total_run [false]
  refine ⟨fuel,hf.trans (by decide),hh,?_⟩
  exact ho

/-- Two fields, including an empty one and a nonpalindromic payload, are both
traversed. The independently specified literal output retains both boundaries. -/
theorem multiple_fields_control :
    ∃ fuel ≤ 10000,
      let c := tick^[fuel]
        (start [true,true,false,false,true,false,true,true,false,false,true,true,false])
      c.l = none ∧ readout c =
        some [true,true,false,false,true,false,true,true,false,false,true,true,false] := by
  obtain ⟨fuel,hf,hh,ho⟩ := total_run
    [true,true,false,false,true,false,true,true,false,false,true,true,false]
  refine ⟨fuel,hf.trans (by decide),hh,?_⟩
  exact ho

/-- A count of two with only one empty field must halt in rejection. -/
theorem missing_field_control :
    ∃ fuel ≤ 2000, let c := tick^[fuel] (start [true,true,false,false,true,false])
      c.l = none ∧ readout c = none := by
  obtain ⟨fuel,hf,hh,ho⟩ := total_run [true,true,false,false,true,false]
  exact ⟨fuel,hf.trans (by decide),hh,ho⟩

/-- The second field has a noncanonical length prefix; a valid first field
cannot make the whole record acceptable. -/
theorem malformed_later_control :
    ∃ fuel ≤ 4000,
      let c := tick^[fuel]
        (start [true,true,false,false,true,false,true,false,false])
      c.l = none ∧ readout c = none := by
  obtain ⟨fuel,hf,hh,ho⟩ := total_run [true,true,false,false,true,false,true,false,false]
  exact ⟨fuel,hf.trans (by decide),hh,ho⟩

/-- Even the empty record rejects an extra bit instead of ignoring its suffix. -/
theorem trailing_input_control :
    ∃ fuel ≤ 200, let c := tick^[fuel] (start [false,true])
      c.l = none ∧ readout c = none := by
  obtain ⟨fuel,hf,hh,ho⟩ := total_run [false,true]
  exact ⟨fuel,hf.trans (by decide),hh,ho⟩

#print axioms count_eligible
#print axioms supports
#print axioms body_run
#print axioms body_rejected
#print axioms loop_run
#print axioms count_run
#print axioms count_rejected
#print axioms total_run
#print axioms cache_run
#print axioms source_cache_run
#print axioms empty_record_control
#print axioms multiple_fields_control
#print axioms missing_field_control
#print axioms malformed_later_control
#print axioms trailing_input_control
end ExplainableCrypto.Helios.Computational.RecordParserMachine
