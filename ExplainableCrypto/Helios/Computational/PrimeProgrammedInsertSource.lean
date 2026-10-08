import ExplainableCrypto.Helios.Computational.PrimeProgrammedStateCallerSource
import ExplainableCrypto.Helios.Computational.BallotStateBitSize
import ExplainableCrypto.Helios.Computational.CacheHashHandler

/-! Actual source operands for the next cache-programming transition.
Arbitrary typed initial caches/flags/history are permitted; no caller presentation
or execution-cost certificate is assumed. Copying, insertion and repacking are
separate executable obligations. -/
namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertSource
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]

abbrev State := BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q)
abbrev Cache := BallotFiniteCache (ZMod q) (PrimeGroup p q)
abbrev Draws := (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)

/-- The exact reached loader state, before the new caller transfers any words. -/
theorem source_fields (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let cfg := PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out
    cfg.l = none ∧ cfg.var = 2 ∧
    cfg.stk 43 = (ballotKeyBitCodec p q).encode (PrimeSimKeySource.key g pk vote out) ∧
    cfg.stk 10 = (primeScalarBitCodec q).encode out.2.1 ∧
    cfg.stk 44 = (ballotCacheBitCodec p q).encode s.cache ∧
    cfg.stk 45 = (ballotCacheBitCodec p q).encode live ∧
    cfg.stk 46 = [s.bad] ∧
    cfg.stk 47 = (ballotStatementBitCodec p q).list.encode s.programmed :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Copy and insertion workspace is derived from the actual full source result. -/
theorem source_work (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (j : Fin 7) :
    (PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out).stk
      ⟨23+j.val,by omega⟩ = [] := by
  fin_cases j <;> rfl

/-- Each bound is charged to its actual stored record size or typed modulus;
these do not replace the enclosing source's separate prefix-size obligations. -/
theorem source_lengths (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let cfg := PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out
    (cfg.stk 43).length ≤ keyRecordBitBound p ∧
    (cfg.stk 10).length ≤ groupRecordBitBound q ∧
    (cfg.stk 44).length ≤ cacheRecordBitBound p q s.cache.entries.length ∧
    (cfg.stk 45).length ≤ cacheRecordBitBound p q live.entries.length ∧
    (cfg.stk 46).length = 1 ∧
    (cfg.stk 47).length ≤ bitListSize (statementRecordBitBound p) s.programmed.length := by
  exact ⟨ballotKeyBits_length_le _,scalarEncode_length_le _,
    ballotCacheBits_length_le _,ballotCacheBits_length_le _,rfl,
    BitRecordCodec.list_length_le _ s.programmed _ _
      (fun stmt _ => ballotStatementBits_length_le stmt) le_rfl⟩

/-- The cache iteration budget can use the loaded word length without a new
caller-supplied entry-count bound. -/
theorem source_entries_le (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    s.cache.entries.length ≤
      ((PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out).stk 44).length :=
  CacheHashHandler.entries_le s.cache

/-- Counted history parsing obtains its loop bound from the actual encoded word. -/
theorem source_history_count_le (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    s.programmed.length ≤
      ((PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out).stk 47).length := by
  change s.programmed.length ≤
    (bitFieldsEncode (s.programmed.map (ballotStatementBitCodec p q).encode)).length
  simpa only [List.length_map] using CacheHashHandler.fields_count_le
    (s.programmed.map (ballotStatementBitCodec p q).encode)

/-- These four actual coordinate words form the original nested statement codec,
not a flat prefix of the complete hash-key encoding. -/
theorem source_statement (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let cfg := PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out
    let stmt := (PrimeSimKeySource.key g pk vote out).1
    cfg.stk 16 = (primeGroupCoordinate stmt.generator).val.bits ∧
    cfg.stk 15 = (primeGroupCoordinate stmt.publicKey).val.bits ∧
    cfg.stk 17 = (primeGroupCoordinate stmt.ciphertext.1).val.bits ∧
    cfg.stk 0 = (primeGroupCoordinate stmt.ciphertext.2).val.bits :=
  ⟨rfl,rfl,rfl,rfl⟩

set_option maxRecDepth 65536 in
/-- Reuse the existing full-key coordinate bound at the reached48-word source. -/
theorem source_statement_widths (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let cfg := PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out
    (cfg.stk 16).length ≤ (p-1).size ∧ (cfg.stk 15).length ≤ (p-1).size ∧
    (cfg.stk 17).length ≤ (p-1).size ∧ (cfg.stk 0).length ≤ (p-1).size := by
  have h := PrimeSimKeySource.source_width slack g pk vote
    (PrimeProgrammedStateSource.saved s live) out
  exact ⟨h _ (by simp only [PrimeSimKeySource.ports,List.map_cons,List.map_nil,List.mem_cons]; exact Or.inl rfl),
    h _ (by simp only [PrimeSimKeySource.ports,List.map_cons,List.map_nil,List.mem_cons]; exact Or.inr (Or.inl rfl)),
    h _ (by simp only [PrimeSimKeySource.ports,List.map_cons,List.map_nil,List.mem_cons]; exact Or.inr (Or.inr (Or.inl rfl))),
    h _ (by simp only [PrimeSimKeySource.ports,List.map_cons,List.map_nil,List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩

/-- Every saved-state payload comes from the retained original raw input.
These bounds make the enclosing execution clock independent of sampled values. -/
theorem source_payload_lengths (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let cfg := PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out
    (cfg.stk 44).length ≤ (cfg.stk 14).length ∧
    (cfg.stk 45).length ≤ (cfg.stk 14).length ∧
    (cfg.stk 47).length ≤ (cfg.stk 14).length := by
  have h := PrimeProgrammedStateInputMachine.payload_lengths (uniformNatEncode p)
    ((ballotCiphertextBitCodec p q).encode (g,pk)) (SamplerOperands.input slack q [])
    [vote] ((ballotCacheBitCodec p q).encode s.cache)
    ((ballotCacheBitCodec p q).encode live) [s.bad]
    ((ballotStatementBitCodec p q).list.encode s.programmed)
  exact ⟨h ((ballotCacheBitCodec p q).encode s.cache) (by simp),
    h ((ballotCacheBitCodec p q).encode live) (by simp),
    h ((ballotStatementBitCodec p q).list.encode s.programmed) (by simp)⟩

/-- The insertion routine's initialized local height has an original-raw-size
bound derived from its actual five records and singleton flag. -/
theorem source_input_bound (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let cfg := PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out
    1+(cfg.stk 44).length+(cfg.stk 10).length+(cfg.stk 43).length+
      (cfg.stk 45).length+(cfg.stk 47).length ≤
    1+3*(cfg.stk 14).length+keyRecordBitBound p+groupRecordBitBound q := by
  obtain ⟨hc,hl,hh⟩ := source_payload_lengths slack g pk vote s live out
  obtain ⟨hk,hv,_⟩ := source_lengths slack g pk vote s live out
  dsimp only at *
  omega

#print axioms source_payload_lengths
#print axioms source_input_bound

/-- Transcript at the actual first simulator key, in existing source order. -/
def transcript (g pk : PrimeGroup p q) (vote : Bool) (out : Draws (q:=q)) :
    BallotCommitment (PrimeGroup p q) × ZMod q × BallotResponse (ZMod q) :=
  ((PrimeSimKeySource.key g pk vote out).2,out.2.1,
    (out.2.2.1,out.2.2.2.1,out.2.2.2.2))

/-- Occupied keys retain their old cache even if the sampled challenge agrees;
sticky bad is set and the exact statement is prepended again. -/
theorem program_occupied (g pk : PrimeGroup p q) (vote : Bool) (out : Draws (q:=q))
    (s : State (p:=p) (q:=q)) (old : ZMod q)
    (h : s.cache.lookup (PrimeSimKeySource.key g pk vote out) = some old) :
    (s.program (PrimeSimKeySource.key g pk vote out).1 (transcript g pk vote out)).2 =
      ⟨s.cache,true,(PrimeSimKeySource.key g pk vote out).1 :: s.programmed⟩ := by
  simp only [BallotFiniteProgrammedState.program,transcript,Prod.mk.eta,h]

/-- Fresh keys insert the actual c; prior bad and ordered repeated history remain. -/
theorem program_fresh (g pk : PrimeGroup p q) (vote : Bool) (out : Draws (q:=q))
    (s : State (p:=p) (q:=q))
    (h : s.cache.lookup (PrimeSimKeySource.key g pk vote out) = none) :
    (s.program (PrimeSimKeySource.key g pk vote out).1 (transcript g pk vote out)).2 =
      ⟨s.cache.insert (PrimeSimKeySource.key g pk vote out) out.2.1,s.bad,
        (PrimeSimKeySource.key g pk vote out).1 :: s.programmed⟩ := by
  simp only [BallotFiniteProgrammedState.program,transcript,Prod.mk.eta,h]

#print axioms source_fields
#print axioms source_work
#print axioms source_lengths
#print axioms source_history_count_le
#print axioms source_statement
#print axioms source_statement_widths
#print axioms source_entries_le
#print axioms program_occupied
#print axioms program_fresh
end ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertSource
