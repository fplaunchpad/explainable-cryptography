import ExplainableCrypto.Helios.Computational.PrimeSecondKeyMachineSource
import ExplainableCrypto.Helios.Computational.PrimeProgramRepackSource

/-! Source inputs for the second programming request. The current resident state
is used directly; the retained original raw input contains stale saved state.
These are semantic/representation/size results, not an executed second update. -/
namespace ExplainableCrypto.Helios.Computational.PrimeSecondProgramSource
open PrimeProgramProofSource (State Cache Draws)
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

def current (g pk : PrimeGroup p q) (vote : Bool) (s : State (p:=p) (q:=q))
    (out : Draws (q:=q)) : State (p:=p) (q:=q) :=
  PrimeProgramRepackSource.nextState g pk vote s out

def statement (g pk : PrimeGroup p q) (out : Draws (q:=q)) :=
  PrimeSecondCommitSource.statement g pk out

def key (g pk : PrimeGroup p q) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) := PrimeSecondKeyMachine.key g pk out cs

def transcript (g pk : PrimeGroup p q) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :=
  (PrimeSecondCommitSource.commitment g pk out cs,cs.1,(cs.2.1,cs.2.2.1,cs.2.2.2))

def next (g pk : PrimeGroup p q) (vote : Bool) (s : State (p:=p) (q:=q))
    (out : Draws (q:=q)) (cs : ZMod q × ZMod q × ZMod q × ZMod q) : State (p:=p) (q:=q) :=
  ((current g pk vote s out).program (statement g pk out) (transcript g pk out cs)).2

/-- The new key and challenge accompany the actual post-p0 state, not the
original input's saved payload. No extraction or presentation premise is supplied. -/
theorem source_fields (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    let cfg := PrimeSecondKeyMachine.sourceResult slack g pk vote s live out cs
    let cur := current g pk vote s out
    cfg.stk 70 = (ballotKeyBitCodec p q).encode (key g pk out cs) ∧
    cfg.stk 54 = scalarEncode cs.1 ∧
    cfg.stk 44 = (ballotCacheBitCodec p q).encode cur.cache ∧
    cfg.stk 45 = (ballotCacheBitCodec p q).encode live ∧
    cfg.stk 46 = [cur.bad] ∧
    cfg.stk 47 = (ballotStatementBitCodec p q).list.encode cur.programmed := by
  have h := PrimeProgramCaller.source_state slack g pk vote s live out
  exact ⟨rfl,rfl,h.1,h.2.2.1,h.2.1,h.2.2.2⟩

theorem source_work (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (j : Fin 7) :
    (PrimeSecondKeyMachine.sourceResult slack g pk vote s live out cs).stk
      ⟨23+j.val,by omega⟩ = [] := by
  fin_cases j <;> rfl

/-- The nested history statement uses p1 ciphertext coordinates, independently
of the flat eight-field key's framing. -/
theorem source_statement (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    let cfg := PrimeSecondKeyMachine.sourceResult slack g pk vote s live out cs
    let stmt := statement g pk out
    cfg.stk 16 = (primeGroupCoordinate stmt.generator).val.bits ∧
    cfg.stk 15 = (primeGroupCoordinate stmt.publicKey).val.bits ∧
    cfg.stk 50 = (primeGroupCoordinate stmt.ciphertext.1).val.bits ∧
    cfg.stk 51 = (primeGroupCoordinate stmt.ciphertext.2).val.bits := ⟨rfl,rfl,rfl,rfl⟩

/-- Current serialized fields agree with saved49; raw14 still encodes the old
initial state. These identities do not claim to execute state deserialization. -/
theorem source_context (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    let cfg := PrimeSecondKeyMachine.sourceResult slack g pk vote s live out cs
    cfg.stk 14 = PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live) ∧
    cfg.stk 49 = (ballotBothCachesBitCodec p q).encode (current g pk vote s out,live) ∧
    cfg.stk 48 = (ballotProofBitCodec p q).encode (PrimeProgramProofSource.proof g pk vote out) :=
  ⟨rfl,rfl,rfl⟩

/-- Updated counts are charged to N+1; the stale initial payload bound N is
not reused for cache/history. -/
theorem source_counts (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let N := (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)).length
    (current g pk vote s out).cache.entries.length ≤ N+1 ∧
    (current g pk vote s out).programmed.length ≤ N+1 ∧ live.entries.length ≤ N :=
  PrimeProgramRepackSource.source_counts slack g pk vote s live out

theorem source_lengths (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    let cfg := PrimeSecondKeyMachine.sourceResult slack g pk vote s live out cs
    let N := (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)).length
    (cfg.stk 70).length ≤ keyRecordBitBound p ∧
    (cfg.stk 54).length ≤ groupRecordBitBound q ∧
    (cfg.stk 44).length ≤ cacheRecordBitBound p q (N+1) ∧
    (cfg.stk 45).length ≤ N ∧ (cfg.stk 46).length = 1 ∧
    (cfg.stk 47).length ≤ bitListSize (statementRecordBitBound p) (N+1) := by
  dsimp only
  obtain ⟨hk,hc,hs,hl,hb,hh⟩ := source_fields slack g pk vote s live out cs
  rw [hk,hc,hs,hl,hb,hh]
  obtain ⟨hcache,hhistory,_⟩ := source_counts slack g pk vote s live out
  have hlive := (PrimeProgrammedInsertSource.source_payload_lengths slack g pk vote s live out).2.1
  exact ⟨ballotKeyBits_length_le _,scalarEncode_length_le _,
    ballotCacheBits_length_le_of_entries _ _ hcache,hlive,rfl,
    BitRecordCodec.list_length_le _ _ _ _ (fun stmt _ => ballotStatementBits_length_le stmt) hhistory⟩

/-- Occupied keys, including agreeing values, retain cache order and set bad;
the original source still prepends the statement to its history. -/
theorem program_occupied (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (old : ZMod q)
    (h : (current g pk vote s out).cache.lookup (key g pk out cs) = some old) :
    next g pk vote s out cs = ⟨(current g pk vote s out).cache,true,
      statement g pk out :: (current g pk vote s out).programmed⟩ := by
  simp only [next,BallotFiniteProgrammedState.program,transcript,key,
    PrimeSecondKeyMachine.key,statement,Prod.mk.eta] at h ⊢
  rw [h]

theorem program_fresh (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q)
    (h : (current g pk vote s out).cache.lookup (key g pk out cs) = none) :
    next g pk vote s out cs = ⟨(current g pk vote s out).cache.insert (key g pk out cs) cs.1,
      (current g pk vote s out).bad,statement g pk out :: (current g pk vote s out).programmed⟩ := by
  simp only [next,BallotFiniteProgrammedState.program,transcript,key,
    PrimeSecondKeyMachine.key,statement,Prod.mk.eta] at h ⊢
  rw [h]

/-- Both lookup branches return the same sampled p1 proof. This is source
semantics only; the p1 returned-proof encoder is a separate remaining operation. -/
theorem program_return (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    ((current g pk vote s out).program (statement g pk out) (transcript g pk out cs)).1 =
      ballotTranscriptProof (PrimeSecondCommitSource.commitment g pk out cs) cs.1
        (cs.2.1,cs.2.2.1,cs.2.2.2) := by
  unfold BallotFiniteProgrammedState.program
  split <;> rfl

theorem next_counts (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    (next g pk vote s out cs).cache.entries.length ≤ (current g pk vote s out).cache.entries.length+1 ∧
    (next g pk vote s out cs).programmed.length = (current g pk vote s out).programmed.length+1 := by
  cases h : (current g pk vote s out).cache.lookup (key g pk out cs) with
  | some old => rw [program_occupied g pk vote s out cs old h]; simp
  | none =>
    have hn : key g pk out cs ∉ (current g pk vote s out).cache := by
      intro hk
      have he := AList.lookup_isSome.mpr hk
      simp [h] at he
    rw [program_fresh g pk vote s out cs h,AList.entries_insert_of_notMem hn,List.length_cons]
    exact ⟨le_rfl,rfl⟩

theorem successor_counts (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    let N := (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)).length
    (next g pk vote s out cs).cache.entries.length ≤ N+2 ∧
    (next g pk vote s out cs).programmed.length ≤ N+2 ∧ live.entries.length ≤ N := by
  obtain ⟨hc,hh,hl⟩ := source_counts slack g pk vote s live out
  obtain ⟨hcn,hhn⟩ := next_counts g pk vote s out cs
  exact ⟨by omega,by omega,hl⟩

#print axioms source_fields
#print axioms source_work
#print axioms source_statement
#print axioms source_context
#print axioms source_counts
#print axioms source_lengths
#print axioms program_occupied
#print axioms program_fresh
#print axioms program_return
#print axioms next_counts
#print axioms successor_counts
end ExplainableCrypto.Helios.Computational.PrimeSecondProgramSource
