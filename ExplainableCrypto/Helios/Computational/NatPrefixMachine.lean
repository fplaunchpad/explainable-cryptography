import ExplainableCrypto.Helios.Computational.BitCopyMachine
import ExplainableCrypto.Helios.Computational.NatPrefixFormat

/-! The existing binary-natural prefix format, parsed by finite-control TM2.
Binary digits are output literally; converting them to a Lean Nat is a semantic
readout, not a machine instruction. -/
namespace ExplainableCrypto.Helios.Computational
namespace NatPrefixMachine
open Turing.TM2

inductive Stack where
  | input | count | scratch | output
  deriving DecidableEq
open Stack
instance : Fintype Stack where
  elems := {input,count,scratch,output}
  complete k := by cases k <;> simp

inductive Label where
  | width | payload | restore
  deriving DecidableEq
open Label
instance : Inhabited Label := ⟨width⟩
instance : Fintype Label where
  elems := {width,payload,restore}
  complete k := by cases k <;> simp

abbrev Config := Cfg (fun _ : Stack => Bool) Label (Option Bool)
private def fail : Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  .load (fun _ => some false) .halt

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | width => .pop input (fun _ b => b) <|
      .branch Option.isSome
        (.branch (fun b => b.getD false)
          (.push count (fun _ => true) (.goto (fun _ => width)))
          (.goto (fun _ => payload))) fail
  | payload => .pop count (fun _ b => b) <|
      .branch Option.isSome
        (.pop input (fun _ b => b) <| .branch Option.isSome
          (.push scratch (fun b => b.getD false) (.goto (fun _ => payload))) fail)
        (.peek scratch (fun _ b => b) <|
          .branch (fun b => decide (b ≠ some false)) (.goto (fun _ => restore)) fail)
  | restore => .pop scratch (fun _ b => b) <|
      .branch Option.isSome
        (.push output (fun b => b.getD false) (.goto (fun _ => restore)))
        (.load (fun _ => some true) .halt)

def config (phase : Option Label) (xs cs zs ys : List Bool)
    (v : Option Bool := none) : Config :=
  ⟨phase,v,fun k => match k with
    | input => xs | count => cs | scratch => zs | output => ys⟩

def start (word : List Bool) : Config := config (some width) word [] [] []
def tick (c : Config) : Config := (step program c).getD c

theorem supports : Supports program Finset.univ := by
  constructor
  · simp
  · intro q _
    cases q <;> simp [program,fail,SupportsStmt]

private theorem width_step (xs cs zs ys : List Bool) (v : Option Bool) :
    tick (config (some width) xs cs zs ys v) = match xs with
      | [] => config none [] cs zs ys (some false)
      | false::bs => config (some payload) bs cs zs ys (some false)
      | true::bs => config (some width) bs (true::cs) zs ys (some true) := by
  cases xs with
  | nil => simp [tick,config,program,fail,stepAux,Function.update]
  | cons b bs =>
    cases b <;> simp [tick,config,program,fail,stepAux]
    all_goals funext k; cases k <;> simp

private theorem payload_empty (xs zs ys : List Bool) (v : Option Bool) :
    tick (config (some payload) xs [] zs ys v) =
      if zs.head? = some false then config none xs [] zs ys (some false)
      else config (some restore) xs [] zs ys zs.head? := by
  simp [tick,config,program,fail,stepAux,Bool.cond_eq_ite,Function.update]

private theorem payload_bit (b : Bool) (xs cs zs ys : List Bool) (v : Option Bool) :
    tick (config (some payload) (b::xs) (true::cs) zs ys v) =
      config (some payload) xs cs (b::zs) ys (some b) := by
  simp [tick,config,program,fail,stepAux]
  funext k
  cases k <;> simp

private theorem payload_missing (cs zs ys : List Bool) (v : Option Bool) :
    tick (config (some payload) [] (true::cs) zs ys v) =
      config none [] cs zs ys (some false) := by
  simp [tick,config,program,fail,stepAux]
  funext k
  cases k <;> simp

private theorem restore_step (xs cs zs ys : List Bool) (v : Option Bool) :
    tick (config (some restore) xs cs zs ys v) = match zs with
      | [] => config none xs cs [] ys (some true)
      | b::bs => config (some restore) xs cs bs (b::ys) (some b) := by
  cases zs with
  | nil => simp [tick,config,program,stepAux,Function.update]
  | cons b bs =>
    simp [tick,config,program,stepAux]
    funext k
    cases k <;> simp

private theorem markers_cons (w : Nat) (cs : List Bool) :
    List.replicate w true ++ true::cs = true::(List.replicate w true ++ cs) := by
  calc
    _ = (List.replicate w true ++ [true]) ++ cs := by simp
    _ = List.replicate (w+1) true ++ cs := by rw [←List.replicate_succ']
    _ = _ := by rw [List.replicate_succ,List.cons_append]

private theorem width_run (w : Nat) (xs cs zs ys : List Bool) (v : Option Bool) :
    tick^[w+1] (config (some width) (List.replicate w true ++ false::xs) cs zs ys v) =
      config (some payload) xs (List.replicate w true ++ cs) zs ys (some false) := by
  induction w generalizing cs v with
  | zero => simp [width_step]
  | succ w ih =>
    rw [Function.iterate_succ_apply]
    simp only [List.replicate_succ,List.cons_append,width_step]
    rw [ih]
    rw [markers_cons]

private theorem payload_run (bs xs cs zs ys : List Bool) (v : Option Bool) :
    ∃ mem, tick^[bs.length] (config (some payload) (bs++xs)
      (List.replicate bs.length true ++ cs) zs ys v) =
      config (some payload) xs cs (bs.reverse++zs) ys mem := by
  induction bs generalizing zs v with
  | nil => exact ⟨v,by simp⟩
  | cons b bs ih =>
    obtain ⟨mem,hm⟩ := ih (b::zs) (some b)
    refine ⟨mem,?_⟩
    rw [List.length_cons,Function.iterate_succ_apply]
    simp only [List.cons_append,List.replicate_succ,payload_bit]
    simpa using hm

private theorem restore_run (xs cs zs ys : List Bool) (v : Option Bool) :
    tick^[zs.length+1] (config (some restore) xs cs zs ys v) =
      config none xs cs [] (zs.reverse++ys) (some true) := by
  induction zs generalizing ys v with
  | nil => simp [restore_step]
  | cons b zs ih =>
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,restore_step,ih]
    simp

/-- Canonical payloads succeed with the original suffix and cleared workspace. -/
theorem frame_run (bs suffix : List Bool) (h : bs.reverse.head? ≠ some false) :
    tick^[3*bs.length+3] (start (List.replicate bs.length true ++ false::(bs++suffix))) =
      config none suffix [] [] bs (some true) := by
  have hn : 3*bs.length+3 = ((bs.length+1)+(bs.length+1))+(bs.length+1) := by omega
  rw [hn,Function.iterate_add_apply tick ((bs.length+1)+(bs.length+1)) (bs.length+1),
    Function.iterate_add_apply tick (bs.length+1) (bs.length+1)]
  unfold start
  rw [width_run]
  obtain ⟨mem,hm⟩ := payload_run bs suffix [] [] [] (some false)
  simp only [List.append_nil] at hm ⊢
  have hp : tick^[bs.length+1] (config (some payload) (bs++suffix)
      (List.replicate bs.length true) [] [] (some false)) =
      config (some restore) suffix [] bs.reverse [] bs.reverse.head? := by
    rw [Function.iterate_succ_apply',hm,payload_empty]
    rw [if_neg h]
  rw [hp]
  simpa using restore_run suffix [] bs.reverse [] bs.reverse.head?

/-- The actual existing encoded natural is parsed with its suffix unchanged. -/
theorem encoded_run (n : Nat) (suffix : List Bool) :
    tick^[3*n.size+3] (start (uniformNatEncode n ++ suffix)) =
      config none suffix [] [] n.bits (some true) := by
  simpa only [uniformNatEncode,List.append_assoc,List.cons_append,Nat.size_eq_bits_len]
    using frame_run n.bits suffix (natPayload_canonical n)

private theorem missing_width (w : Nat) (cs zs ys : List Bool) (v : Option Bool) :
    tick^[w+1] (config (some width) (List.replicate w true) cs zs ys v) =
      config none [] (List.replicate w true ++ cs) zs ys (some false) := by
  induction w generalizing cs v with
  | zero => simp [width_step]
  | succ w ih =>
    rw [Function.iterate_succ_apply]
    simp only [List.replicate_succ,width_step]
    rw [ih,markers_cons]
    rfl

theorem no_delimiter_run (w : Nat) :
    tick^[w+1] (start (List.replicate w true)) =
      config none [] (List.replicate w true) [] [] (some false) := by
  simpa only [start,List.append_nil] using missing_width w [] [] [] none

private theorem short_payload (bs : List Bool) (k : Nat) (zs ys : List Bool) (v : Option Bool) :
    tick^[bs.length+1] (config (some payload) bs
      (List.replicate (bs.length+(k+1)) true) zs ys v) =
      config none [] (List.replicate k true) (bs.reverse++zs) ys (some false) := by
  obtain ⟨mem,hm⟩ := payload_run bs [] (List.replicate (k+1) true) zs ys v
  simp only [List.append_nil,←List.replicate_add] at hm
  rw [Function.iterate_succ_apply',hm]
  simp only [List.replicate_succ,payload_missing]

theorem truncated_run (w : Nat) (bs : List Bool) (h : bs.length < w) :
    let out := tick^[w+bs.length+2] (start (List.replicate w true ++ false::bs))
    out.l = none ∧ out.var = some false := by
  let k := w-bs.length-1
  have hw : w = bs.length+(k+1) := by dsimp [k]; omega
  have hn : w+bs.length+2 = (bs.length+1)+(w+1) := by omega
  rw [hn,Function.iterate_add_apply tick (bs.length+1) (w+1)]
  unfold start
  rw [width_run]
  simp only [List.append_nil]
  rw [hw,short_payload]
  exact ⟨rfl,rfl⟩

theorem noncanonical_run (bs suffix : List Bool) (h : bs.reverse.head? = some false) :
    tick^[2*bs.length+2] (start (List.replicate bs.length true ++ false::(bs++suffix))) =
      config none suffix [] bs.reverse [] (some false) := by
  have hn : 2*bs.length+2 = (bs.length+1)+(bs.length+1) := by omega
  rw [hn,Function.iterate_add_apply tick (bs.length+1) (bs.length+1)]
  unfold start
  rw [width_run]
  obtain ⟨mem,hm⟩ := payload_run bs suffix [] [] [] (some false)
  simp only [List.append_nil] at hm ⊢
  rw [Function.iterate_succ_apply',hm,payload_empty,if_pos h]

/-- Accepted words of the original reader have a concrete parser run; no
structural/canonicality premise is left for the caller to establish. -/
theorem accepted_run (word : List Bool) (n : Nat) (suffix : List Bool)
    (h : uniformNatRead word = some (n,suffix)) :
    tick^[3*n.size+3] (start word) = config none suffix [] [] n.bits (some true) := by
  rw [uniformNatRead_exact word n suffix h]
  exact encoded_run n suffix

/-- Read the output tapes only after successful halt. -/
def readout (c : Config) : Option (List Bool × List Bool) :=
  if c.l = none ∧ c.var = some true then some (c.stk output,c.stk input) else none

private theorem header_cases (word : List Bool) :
    (∃ w, word = List.replicate w true) ∨
      ∃ w xs, word = List.replicate w true ++ false::xs := by
  induction word with
  | nil => exact Or.inl ⟨0,rfl⟩
  | cons b word ih =>
    cases b with
    | false => exact Or.inr ⟨0,word,rfl⟩
    | true =>
      rcases ih with ⟨w,rfl⟩ | ⟨w,xs,rfl⟩
      · exact Or.inl ⟨w+1,rfl⟩
      · exact Or.inr ⟨w+1,xs,rfl⟩

/-- All raw input words halt within a derived linear bound and agree exactly
with the original prefix decoder, returning literal binary digits and suffix.
No well-formedness or successful-decoding premise is required. -/
theorem total_run (word : List Bool) :
    ∃ fuel ≤ 3*word.length+3,
      let c := tick^[fuel] (start word)
      c.l = none ∧ readout c = (uniformNatRead word).map (fun p => (p.1.bits,p.2)) := by
  rcases header_cases word with ⟨w,rfl⟩ | ⟨w,bs,rfl⟩
  · refine ⟨w+1,?_,?_⟩
    · simp only [List.length_replicate]; omega
    · rw [no_delimiter_run,uniformNatRead_no_delimiter]
      simp [readout,config]
  · by_cases hs : bs.length < w
    · refine ⟨w+bs.length+2,?_,(truncated_run w bs hs).1,?_⟩
      · simp only [List.length_append,List.length_replicate,List.length_cons]; omega
      · rw [uniformNatRead_truncated w bs hs]
        simp only [readout,(truncated_run w bs hs).2]
        simp
    · obtain ⟨bits,suffix,rfl,hw⟩ : ∃ bits suffix,
          bs = bits++suffix ∧ bits.length = w :=
        ⟨bs.take w,bs.drop w,(List.take_append_drop w bs).symm,
          List.length_take_of_le (Nat.le_of_not_gt hs)⟩
      subst w
      by_cases hc : bits.reverse.head? = some false
      · refine ⟨2*bits.length+2,?_,?_⟩
        · simp only [List.length_append,List.length_replicate,List.length_cons]; omega
        · rw [noncanonical_run bits suffix hc,uniformNatRead_frame,if_pos hc]
          simp [readout,config]
      · refine ⟨3*bits.length+3,?_,?_⟩
        · simp only [List.length_append,List.length_replicate,List.length_cons]; omega
        · rw [frame_run bits suffix hc,uniformNatRead_frame,if_neg hc]
          simp [readout,config,natPayload_value_bits bits hc]

/-- Parse the existing cache's actual outer count field, preserving every
remaining entry/framing bit. The prefix is extracted from the concrete encoder. -/
theorem cache_header_run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q)) :
    ∃ rest, (ballotCacheBitCodec p q).encode cache = uniformNatEncode cache.entries.length ++ rest ∧
      tick^[3*cache.entries.length.size+3] (start ((ballotCacheBitCodec p q).encode cache)) =
        config none rest [] [] cache.entries.length.bits (some true) := by
  have he : (ballotCacheBitCodec p q).encode cache =
      bitFieldsEncode (cache.entries.map (ballotCacheEntryBitCodec p q).encode) := rfl
  unfold bitFieldsEncode at he
  simp only [List.length_map] at he
  refine ⟨_,he,?_⟩
  rw [he]
  exact encoded_run _ _

open OracleComp OracleSpec

/-- The actual explicit source derives the binary count-field parsing budget. -/
theorem source_cache_header {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2))
    (n : Nat) (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (out : RepairedSubmissionResult (ZMod q) (PrimeGroup p q) ×
      BallotFiniteLoggedState (ZMod q) (PrimeGroup p q))
    (ho : out ∈ support (runBallotFiniteLogged
      (repairedSubmissionPrimeSourceOracle g pk vote attacker) (∅,[]))) :
    ∃ fuel ≤ 3*(n+15).size+3, ∃ rest,
      (ballotCacheBitCodec p q).encode out.2.1 = uniformNatEncode out.2.1.entries.length ++ rest ∧
      tick^[fuel] (start ((ballotCacheBitCodec p q).encode out.2.1)) =
        config none rest [] [] out.2.1.entries.length.bits (some true) := by
  have hc := runBallotFiniteLogged_cache_length_le _ (n+15)
    (repairedSubmissionPrimeSource_query_bound g pk vote attacker n hb) (∅,[]) out ho
  simp only [AList.empty_entries,List.length_nil,Nat.zero_add] at hc
  refine ⟨_,?_,cache_header_run out.2.1⟩
  have hs := Nat.size_le_size hc
  omega

theorem suffix_control :
    tick^[12] (start [true,true,true,false,false,true,true,true,false]) =
      config none [true,false] [] [] [false,true,true] (some true) := by
  exact encoded_run 6 [true,false]

theorem zero_control :
    tick^[3] (start [false,true,false]) =
      config none [true,false] [] [] [] (some true) := by
  exact encoded_run 0 [true,false]

theorem malformed_controls :
    readout (tick^[3] (start [true,true])) = none ∧
    readout (tick^[3] (start [true,false])) = none ∧
    readout (tick^[4] (start [true,false,false])) = none := by decide

theorem payload_order_control :
    (tick^[12] (start [true,true,true,false,false,true,true])).stk output ≠
      [true,true,false] := by decide

#print axioms supports
#print axioms frame_run
#print axioms encoded_run
#print axioms no_delimiter_run
#print axioms truncated_run
#print axioms noncanonical_run
#print axioms accepted_run
#print axioms total_run
#print axioms cache_header_run
#print axioms source_cache_header
#print axioms suffix_control
#print axioms zero_control
#print axioms malformed_controls
#print axioms payload_order_control
end NatPrefixMachine
end ExplainableCrypto.Helios.Computational
