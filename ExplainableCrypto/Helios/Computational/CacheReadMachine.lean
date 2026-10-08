import ExplainableCrypto.Helios.Computational.CacheLookupMachine

/-! Decode the actual scalar archive after lookup on the same eight stacks.
The hit workspace is derived from execution. No scalar-word reload is used. -/
namespace ExplainableCrypto.Helios.Computational.CacheReadMachine
open Turing.TM2
abbrev Stack := CacheLookupMachine.Stack
abbrev query := CacheLookupMachine.query
abbrev saved := CacheLookupMachine.saved
abbrev digits := CacheLookupMachine.out
abbrev archive := CacheLookupMachine.archive

def parseLayout := CacheLookupMachine.fieldLayout.trans
  (Equiv.swap CacheLookupMachine.src CacheLookupMachine.archive)

inductive Label where
  | lookup (l : CacheLookupMachine.Label) | parse (l : NatPrefixMachine.Label)
  | looked | parsed
  deriving DecidableEq
open Label
instance : Inhabited Label := ⟨lookup default⟩
instance : Fintype Label where
  elems := Finset.univ.image lookup ∪ Finset.univ.image parse ∪ {looked,parsed}
  complete l := by cases l <;> simp
abbrev Config := Cfg (fun _ : Stack => Bool) Label (Option Bool)
private def invalid : Stmt (fun _ : Stack => Bool) Label (Option Bool) := .load (fun _ => none) .halt

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | lookup l => TM2ReturnLink.redirect lookup looked (CacheLookupMachine.program l)
  | parse l => TM2ReturnLink.redirect parse parsed (TM2StackFrame.relocate parseLayout (NatPrefixMachine.program l))
  | looked => .branch Option.isSome
      (.branch (fun v => v.getD false)
        (.load (fun _ => none) (.goto (fun _ => parse default)))
        (.load (fun _ => some false) .halt)) invalid
  | parsed => .branch (fun v => decide (v = some true))
      (.peek archive (fun _ b => b) <| .branch Option.isSome invalid (.load (fun _ => some true) .halt)) invalid

def tick (c : Config) : Config := (step program c).getD c

def state (phase : Option Label) (q tail value counter scalar cache : List Bool) (v : Option Bool) : Config :=
  ⟨phase,v,(CacheLookupMachine.state none q tail [] [] value counter scalar cache v).stk⟩
def start (q cache : List Bool) : Config :=
  TM2ReturnLink.embed lookup looked (CacheLookupMachine.start q cache)

def readout (c : Config) : Option (Option (List Bool)) :=
  if c.l = none then
    match c.var with
    | none => none | some false => some none | some true => some (some (c.stk digits))
  else none

private theorem redirect_supports {L : Type*} (f : L → Label) (ret : Label)
    (s : Stmt (fun _ : Stack => Bool) L (Option Bool)) :
    SupportsStmt Finset.univ (TM2ReturnLink.redirect f ret s) := by
  induction s <;> simp_all [TM2ReturnLink.redirect,SupportsStmt]

theorem supports : Supports program Finset.univ := by
  constructor
  · simp
  · intro l _; cases l <;> simp [program,invalid,redirect_supports,SupportsStmt]

private theorem lookup_run (fuel : Nat) (q cache : List Bool)
    (hh : (CacheLookupMachine.tick^[fuel] (CacheLookupMachine.start q cache)).l = none) :
    ∃ used ≤ fuel, tick^[used] (start q cache) =
      TM2ReturnLink.embed lookup looked (CacheLookupMachine.tick^[fuel] (CacheLookupMachine.start q cache)) := by
  exact TM2ReturnLink.run CacheLookupMachine.program program lookup looked (fun _ => rfl)
    fuel (CacheLookupMachine.start q cache) hh

private theorem parse_run (n : Nat) (q tail counter cache : List Bool) :
    ∃ fuel ≤ 3*n.size+3,
      tick^[fuel] (state (some (parse default)) q tail [] counter (uniformNatEncode n) cache none) =
        state (some parsed) q tail n.bits counter [] cache (some true) := by
  have hr := NatPrefixMachine.encoded_run n []
  simp only [List.append_nil] at hr
  let frame := CacheLookupMachine.fieldFrame q counter tail cache
  have he := TM2StackFrame.run parseLayout NatPrefixMachine.program (3*n.size+3)
    (NatPrefixMachine.start (uniformNatEncode n)) frame
  have hh : ((TM2ReturnLink.tick (fun l => TM2StackFrame.relocate parseLayout (NatPrefixMachine.program l)))^[3*n.size+3]
      (TM2StackFrame.embed parseLayout (NatPrefixMachine.start (uniformNatEncode n)) frame)).l = none := by
    rw [he]
    change (NatPrefixMachine.tick^[3*n.size+3] (NatPrefixMachine.start (uniformNatEncode n))).l = none
    rw [hr]; rfl
  obtain ⟨u,hu,h⟩ := TM2ReturnLink.run (fun l => TM2StackFrame.relocate parseLayout (NatPrefixMachine.program l))
    program parse parsed (fun _ => rfl) (3*n.size+3)
    (TM2StackFrame.embed parseLayout (NatPrefixMachine.start (uniformNatEncode n)) frame) hh
  rw [he] at h
  change tick^[u] _ = TM2ReturnLink.embed parse parsed
    (TM2StackFrame.embed parseLayout (NatPrefixMachine.tick^[3*n.size+3] _) _) at h
  rw [hr] at h
  have hs : TM2ReturnLink.embed parse parsed (TM2StackFrame.embed parseLayout
      (NatPrefixMachine.start (uniformNatEncode n)) frame) =
      state (some (parse default)) q tail [] counter (uniformNatEncode n) cache none := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    rcases k with (((k|b)|⟨⟩)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl
    · rfl
  rw [hs] at h
  refine ⟨u,hu,h.trans ?_⟩
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k
  rcases k with (((k|b)|⟨⟩)|⟨⟩)
  · cases k <;> rfl
  · cases b <;> rfl
  · rfl
  · rfl

def cost (p q N W : Nat) : Nat :=
  2*W+3*N.size+N*CacheLookupMachine.iterationCost p q N+3*(q-1).size+13

/-- A miss clears every work port, retaining the original query and cache. -/
theorem miss_run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q)) (key : BallotForkPoint (PrimeGroup p q))
    (h : cache.lookup key = none) :
    ∃ fuel ≤ cost p q cache.entries.length ((ballotCacheBitCodec p q).encode cache).length,
      tick^[fuel] (start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)) =
        state none ((ballotKeyBitCodec p q).encode key) [] [] [] []
          ((ballotCacheBitCodec p q).encode cache) (some false) := by
  obtain ⟨j,hj,hr⟩ := CacheLookupMachine.miss_run cache key h
  have hh : (CacheLookupMachine.tick^[j]
      (CacheLookupMachine.start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache))).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := lookup_run j ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache) hh
  rw [hr] at he
  refine ⟨u+1,by unfold cost; omega,?_⟩
  rw [Function.iterate_succ_apply',he]
  rfl

/-- The hit post-state exposes the unread suffix and counter. Callers must clear
these ports before a routine requiring empty scratch; the scalar is already parsed. -/
theorem hit_run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q)) (key : BallotForkPoint (PrimeGroup p q))
    (a : ZMod q) (h : cache.lookup key = some a) :
    ∃ fuel ≤ cost p q cache.entries.length ((ballotCacheBitCodec p q).encode cache).length,
      ∃ n tail,
      tick^[fuel] (start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)) =
        state none ((ballotKeyBitCodec p q).encode key) tail a.val.bits (n+1).bits []
          ((ballotCacheBitCodec p q).encode cache) (some true) := by
  obtain ⟨j,hj,n,tail,hr⟩ := CacheLookupMachine.hit_run cache key a h
  have hh : (CacheLookupMachine.tick^[j]
      (CacheLookupMachine.start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache))).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := lookup_run j ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache) hh
  rw [hr] at he
  change tick^[u] _ = state (some looked) ((ballotKeyBitCodec p q).encode key) tail []
    (n+1).bits (scalarEncode a) ((ballotCacheBitCodec p q).encode cache) (some true) at he
  obtain ⟨v,hv,hvRun⟩ := parse_run a.val ((ballotKeyBitCodec p q).encode key) tail (n+1).bits
    ((ballotCacheBitCodec p q).encode cache)
  have enter : tick (state (some looked) ((ballotKeyBitCodec p q).encode key) tail []
      (n+1).bits (scalarEncode a) ((ballotCacheBitCodec p q).encode cache) (some true)) =
    state (some (parse default)) ((ballotKeyBitCodec p q).encode key) tail [] (n+1).bits
      (scalarEncode a) ((ballotCacheBitCodec p q).encode cache) none := rfl
  have finishStep : tick (state (some parsed) ((ballotKeyBitCodec p q).encode key) tail a.val.bits
      (n+1).bits [] ((ballotCacheBitCodec p q).encode cache) (some true)) =
    state none ((ballotKeyBitCodec p q).encode key) tail a.val.bits (n+1).bits []
      ((ballotCacheBitCodec p q).encode cache) (some true) := rfl
  have hs := Nat.size_le_size (Nat.le_sub_one_of_lt a.val_lt)
  refine ⟨(v+1)+(u+1),by unfold cost; omega,n,tail,?_⟩
  rw [Function.iterate_add_apply,Function.iterate_succ_apply' tick u,he,enter,
    Function.iterate_succ_apply' tick v]
  simp only [scalarEncode] at *
  rw [hvRun,finishStep]


/-- Lookup and answer parsing execute in one program. The hit/absence premise
and parser workspace are derived; zero is returned as a hit with empty digits. -/
theorem run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q)) (key : BallotForkPoint (PrimeGroup p q)) :
    ∃ fuel ≤ cost p q cache.entries.length ((ballotCacheBitCodec p q).encode cache).length,
      let c := tick^[fuel] (start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache))
      c.l = none ∧ readout c = some ((cache.lookup key).map (fun a => a.val.bits)) ∧
        c.stk query = (ballotKeyBitCodec p q).encode key ∧ c.stk saved = (ballotCacheBitCodec p q).encode cache := by
  cases h : cache.lookup key with
  | none =>
    obtain ⟨fuel,hf,hr⟩ := miss_run cache key h
    refine ⟨fuel,hf,?_⟩
    dsimp only
    rw [hr]
    exact ⟨rfl,rfl,rfl,rfl⟩
  | some a =>
    obtain ⟨fuel,hf,n,tail,hr⟩ := hit_run cache key a h
    refine ⟨fuel,hf,?_⟩
    dsimp only
    rw [hr]
    exact ⟨rfl,rfl,rfl,rfl⟩

/-- Monotonicity supplies fixed fuel from loaded size and reachable source bounds. -/
theorem cost_mono {p q N M W V : Nat} (hn : N ≤ M) (hw : W ≤ V) :
    cost p q N W ≤ cost p q M V := by
  have hs := Nat.size_le_size hn
  have hi : CacheLookupMachine.iterationCost p q N ≤ CacheLookupMachine.iterationCost p q M := by
    unfold CacheLookupMachine.iterationCost; omega
  have hm := Nat.mul_le_mul hn hi
  unfold cost; omega

open OracleComp OracleSpec

/-- Entry and bit bounds come from supported executions of the repaired source. -/
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
    ∃ fuel ≤ cost p q (n+15) (cacheRecordBitBound p q (n+15)),
      let c := tick^[fuel] (start ((ballotKeyBitCodec p q).encode queryKey)
        ((ballotCacheBitCodec p q).encode result.2.1))
      c.l = none ∧ readout c = some ((result.2.1.lookup queryKey).map (fun a => a.val.bits)) ∧
        c.stk query = (ballotKeyBitCodec p q).encode queryKey ∧
        c.stk saved = (ballotCacheBitCodec p q).encode result.2.1 := by
  obtain ⟨fuel,hf,hr⟩ := run result.2.1 queryKey
  have hw := repairedSubmissionPrime_cache_bits_le g pk vote attacker n hb result hs
  have hn := runBallotFiniteLogged_cache_length_le _ (n+15)
    (repairedSubmissionPrimeSource_query_bound g pk vote attacker n hb) (∅,[]) result hs
  simp only [AList.empty_entries,List.length_nil,Nat.zero_add] at hn
  exact ⟨fuel,hf.trans (cost_mono hn hw),hr⟩

private def fixture (a : ZMod 11) : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11) :=
  AList.singleton BallotCacheCodecControls.key a
private def fixtureBound (a : ZMod 11) : Nat :=
  cost 23 11 1 ((ballotCacheBitCodec 23 11).encode (fixture a)).length

/-- Six has nonpalindromic little-endian digits; the scalar prefix is consumed. -/
theorem hit_control :
    ∃ fuel ≤ fixtureBound 6,
      let c := tick^[fuel] (start ((ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.key)
        ((ballotCacheBitCodec 23 11).encode (fixture 6)))
      c.l = none ∧ readout c = some (some [false,true,true]) ∧
        c.stk query = (ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.key ∧
        c.stk saved = (ballotCacheBitCodec 23 11).encode (fixture 6) := by
  obtain ⟨u,hu,hh,ho,hq,hc⟩ := run (fixture 6) BallotCacheCodecControls.key
  have he : (fixture 6).lookup BallotCacheCodecControls.key = some 6 := by decide
  rw [he] at ho
  exact ⟨u,hu,hh,ho,hq,hc⟩

/-- The empty digit word is a successful zero answer, distinct from absence. -/
theorem zero_control :
    ∃ fuel ≤ fixtureBound 0,
      let c := tick^[fuel] (start ((ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.key)
        ((ballotCacheBitCodec 23 11).encode (fixture 0)))
      c.l = none ∧ readout c = some (some []) ∧ readout c ≠ some none ∧
        c.stk query = (ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.key ∧
        c.stk saved = (ballotCacheBitCodec 23 11).encode (fixture 0) := by
  obtain ⟨u,hu,hh,ho,hq,hc⟩ := run (fixture 0) BallotCacheCodecControls.key
  have he : (fixture 0).lookup BallotCacheCodecControls.key = some 0 := by decide
  rw [he] at ho
  refine ⟨u,hu,hh,ho,?_,hq,hc⟩
  rw [ho]; decide

/-- A different full query on that zero-valued cache reports absence. -/
theorem miss_control :
    ∃ fuel ≤ fixtureBound 0,
      let c := tick^[fuel] (start ((ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.otherKey)
        ((ballotCacheBitCodec 23 11).encode (fixture 0)))
      c.l = none ∧ readout c = some none ∧
        c.stk query = (ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.otherKey ∧
        c.stk saved = (ballotCacheBitCodec 23 11).encode (fixture 0) := by
  obtain ⟨u,hu,hh,ho,hq,hc⟩ := run (fixture 0) BallotCacheCodecControls.otherKey
  have he : (fixture 0).lookup BallotCacheCodecControls.otherKey = none := by decide
  rw [he] at ho
  exact ⟨u,hu,hh,ho,hq,hc⟩

/-- Complete framed answers still reject missing/truncated/noncanonical prefixes
and trailing scalar data; public query and saved cache survive rejection. -/
theorem malformed_controls :
    ∀ bad ∈ ([[],[false,true],[true],[true,false,false]] : List (List Bool)),
      let word := bitFieldsEncode [bitFieldsEncode [[true],bad]]
      let c := tick^[400] (start [true] word)
      c.l = none ∧ readout c = none ∧ c.stk query = [true] ∧ c.stk saved = word := by
  decide +kernel

#print axioms supports
#print axioms run
#print axioms cost_mono
#print axioms source_cache_run
#print axioms hit_control
#print axioms zero_control
#print axioms miss_control
#print axioms malformed_controls
end ExplainableCrypto.Helios.Computational.CacheReadMachine
