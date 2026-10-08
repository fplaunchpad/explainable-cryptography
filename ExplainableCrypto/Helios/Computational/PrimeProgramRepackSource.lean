import ExplainableCrypto.Helios.Computational.PrimeProgramCallerSource

/-! The next saved-state record, derived from the actual resident programming
successor. This module specifies shape and bounds; it does not execute repacking. -/
namespace ExplainableCrypto.Helios.Computational.PrimeProgramRepackSource
open PrimeProgrammedInsertSource
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
set_option maxRecDepth 65536

def nextState (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (out : Draws (q:=q)) : State (p:=p) (q:=q) :=
  (s.program (PrimeSimKeySource.key g pk vote out).1 (transcript g pk vote out)).2

/-- Exact nested codec from updated resident fields, retaining the separate live cache. -/
theorem source_shape (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let cfg := PrimeProgramCaller.sourceResult slack g pk vote s live out
    (ballotBothCachesBitCodec p q).encode (nextState g pk vote s out,live) =
      bitFieldsEncode [bitFieldsEncode [cfg.stk 44,
        bitFieldsEncode [cfg.stk 46,cfg.stk 47]],cfg.stk 45] := by
  dsimp only
  obtain ⟨hc,hb,hl,hh⟩ := PrimeProgramCaller.source_state slack g pk vote s live out
  rw [hc,hb,hl,hh]
  rfl

/-- Occupied cache ordering is retained; history still grows, even for agreeing values. -/
theorem next_occupied (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (out : Draws (q:=q)) (old : ZMod q)
    (h : s.cache.lookup (PrimeSimKeySource.key g pk vote out) = some old) :
    nextState g pk vote s out =
      ⟨s.cache,true,(PrimeSimKeySource.key g pk vote out).1 :: s.programmed⟩ :=
  program_occupied g pk vote out s old h

theorem next_fresh (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (out : Draws (q:=q))
    (h : s.cache.lookup (PrimeSimKeySource.key g pk vote out) = none) :
    nextState g pk vote s out =
      ⟨s.cache.insert (PrimeSimKeySource.key g pk vote out) out.2.1,s.bad,
        (PrimeSimKeySource.key g pk vote out).1 :: s.programmed⟩ :=
  program_fresh g pk vote out s h

/-- One actual programming call increases cache count by at most one and history
count by exactly one. The lookup branches are retained explicitly. -/
theorem next_counts (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (out : Draws (q:=q)) :
    (nextState g pk vote s out).cache.entries.length ≤ s.cache.entries.length+1 ∧
    (nextState g pk vote s out).programmed.length = s.programmed.length+1 := by
  cases h : s.cache.lookup (PrimeSimKeySource.key g pk vote out) with
  | some old => rw [next_occupied g pk vote s out old h]; simp
  | none =>
    have hn : PrimeSimKeySource.key g pk vote out ∉ s.cache := by
      intro hk
      have he := AList.lookup_isSome.mpr hk
      simp [h] at he
    rw [next_fresh g pk vote s out h,AList.entries_insert_of_notMem hn,List.length_cons]
    exact ⟨le_rfl,rfl⟩

/-- Updated counts are bounded by the original input plus one, not its unchanged
old payload bound. -/
theorem source_counts (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let N := (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)).length
    (nextState g pk vote s out).cache.entries.length ≤ N+1 ∧
    (nextState g pk vote s out).programmed.length ≤ N+1 ∧ live.entries.length ≤ N := by
  obtain ⟨hc,hl,hh⟩ := source_payload_lengths slack g pk vote s live out
  have hs := source_entries_le slack g pk vote s live out
  have ht := source_history_count_le slack g pk vote s live out
  have hv := CacheHashHandler.entries_le live
  have hn := next_counts g pk vote s out
  change ((ballotCacheBitCodec p q).encode s.cache).length ≤ _ at hc
  change ((ballotCacheBitCodec p q).encode live).length ≤ _ at hl
  change ((ballotStatementBitCodec p q).list.encode s.programmed).length ≤ _ at hh
  change s.cache.entries.length ≤ ((ballotCacheBitCodec p q).encode s.cache).length at hs
  change s.programmed.length ≤ ((ballotStatementBitCodec p q).list.encode s.programmed).length at ht
  exact ⟨hn.1.trans (Nat.add_le_add_right (hs.trans hc) 1),
    hn.2.le.trans (Nat.add_le_add_right (ht.trans hh) 1),hv.trans hl⟩

/-- Separate growth bounds for every payload consumed by the concrete repacker. -/
theorem source_lengths (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let N := (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)).length
    let cfg := PrimeProgramCaller.sourceResult slack g pk vote s live out
    (cfg.stk 44).length ≤ cacheRecordBitBound p q (N+1) ∧
    (cfg.stk 45).length ≤ cacheRecordBitBound p q N ∧
    (cfg.stk 46).length = 1 ∧
    (cfg.stk 47).length ≤ bitListSize (statementRecordBitBound p) (N+1) := by
  dsimp only
  obtain ⟨hc,hb,hl,hh⟩ := PrimeProgramCaller.source_state slack g pk vote s live out
  rw [hc,hb,hl,hh]
  obtain ⟨hs,ht,hv⟩ := source_counts slack g pk vote s live out
  exact ⟨ballotCacheBits_length_le_of_entries _ _ hs,
    ballotCacheBits_length_le_of_entries _ _ hv,rfl,
    BitRecordCodec.list_length_le _ _ _ _ (fun stmt _ => ballotStatementBits_length_le stmt) ht⟩

/-- Existing complete-state framing gives a uniform next-record bound. -/
theorem saved_length (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let N := (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)).length
    ((ballotBothCachesBitCodec p q).encode (nextState g pk vote s out,live)).length ≤
      bothCachesBitBound p q (N+1) (N+1) N := by
  obtain ⟨hc,hh,hl⟩ := source_counts slack g pk vote s live out
  exact ballotBothCachesBits_length_le _ _ _ _ hc hh hl

/-- The old saved record is stale after every programming call: even occupied
keys prepend history. This excludes reusing the old serialized state. -/
theorem saved_changed (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    (ballotBothCachesBitCodec p q).encode (nextState g pk vote s out,live) ≠
      PrimeProgrammedStateSource.saved s live := by
  intro he
  have hd := congrArg (ballotBothCachesBitCodec p q).decode he
  change (ballotBothCachesBitCodec p q).decode ((ballotBothCachesBitCodec p q).encode _) =
    (ballotBothCachesBitCodec p q).decode ((ballotBothCachesBitCodec p q).encode _) at hd
  rw [BitRecordCodec.roundTrip,BitRecordCodec.roundTrip] at hd
  have ht := congrArg (fun x => x.1.programmed.length) (Option.some.inj hd)
  dsimp only at ht
  have hn := (next_counts g pk vote s out).2
  omega

#print axioms source_shape
#print axioms next_occupied
#print axioms next_fresh
#print axioms next_counts
#print axioms source_counts
#print axioms source_lengths
#print axioms saved_length
#print axioms saved_changed
end ExplainableCrypto.Helios.Computational.PrimeProgramRepackSource
