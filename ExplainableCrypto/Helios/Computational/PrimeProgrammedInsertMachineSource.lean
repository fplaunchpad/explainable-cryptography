import ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertMachineRun
import ExplainableCrypto.Helios.Computational.CacheProgrammedInsertMachineRun

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertMachine
open OracleComp OracleSpec BitOracleMachine
set_option maxHeartbeats 400000
set_option maxRecDepth 65536
attribute [local irreducible] BitOracleMachine.run
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]

/-- Full successor after actual insertion and cleanup. The history word is
updated by the following history routine, whose workspace is restored here. -/
def sourceResult (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : PrimeProgrammedInsertSource.State (p:=p) (q:=q))
    (live : PrimeProgrammedInsertSource.Cache (p:=p) (q:=q))
    (out : PrimeProgrammedInsertSource.Draws (q:=q)) : Config :=
  let key := PrimeSimKeySource.key g pk vote out
  ⟨none,2,Function.update
    (Function.update (PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out).stk
      44 ((ballotCacheBitCodec p q).encode
        (CacheProgrammedInsertMachine.programmedCache s.cache key out.2.1)))
    46 [s.bad || !(s.cache.lookup key).isNone]⟩

/-- The cache update is executed from the actual extracted source state, with
all scratch, entry-count and input-height premises derived from that source. -/
theorem charged_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : PrimeProgrammedInsertSource.State (p:=p) (q:=q))
    (live : PrimeProgrammedInsertSource.Cache (p:=p) (q:=q))
    (out : PrimeProgrammedInsertSource.Draws (q:=q)) :
    let raw := PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)
    ∃ charge ≤ cost p q raw.length,
      BitOracleMachine.run code (clock p q raw.length)
        (start (PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out).stk) =
      pure (sourceResult slack g pk vote s live out,charge) := by
  dsimp only
  let old := (PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out).stk
  let raw := PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)
  have hraw : old 14 = raw := rfl
  have hw (j : Fin 7) : old ⟨23+j.val,by omega⟩ = [] :=
    PrimeProgrammedInsertSource.source_work slack g pk vote s live out j
  obtain ⟨hcache,_,_⟩ := PrimeProgrammedInsertSource.source_payload_lengths slack g pk vote s live out
  change (old 44).length ≤ (old 14).length at hcache
  rw [hraw] at hcache
  have hn := (PrimeProgrammedInsertSource.source_entries_le slack g pk vote s live out).trans hcache
  have hI : CacheProgrammedInsertMachine.insertionFuel s.cache ≤ insertBound p q raw.length :=
    CacheInsertMachine.cost_mono hn hcache
  have hH : CacheProgrammedInsertMachine.canonicalInputBound s.cache
      (PrimeSimKeySource.key g pk vote out) out.2.1
      ((ballotCacheBitCodec p q).encode live)
      ((ballotStatementBitCodec p q).list.encode s.programmed) ≤ inputBound p q raw.length :=
    PrimeProgrammedInsertSource.source_input_bound slack g pk vote s live out
  have hc := CacheProgrammedInsertMachine.charged_bounded s.cache
    (PrimeSimKeySource.key g pk vote out) out.2.1
    ((ballotCacheBitCodec p q).encode live)
    ((ballotStatementBitCodec p q).list.encode s.programmed) s.bad
    (insertBound p q raw.length) (inputBound p q raw.length) hI hH
  obtain ⟨charge,hcharge,he⟩ := charged_link old raw.length (coreClock p q raw.length)
    (CacheProgrammedInsertMachine.cost (insertBound p q raw.length) (inputBound p q raw.length))
    (hw 0) (hw 1) hcache _ _ (frame old)
    (source_return slack g pk vote s live out) rfl hc
  have hout := core_result old
    ((ballotCacheBitCodec p q).encode (CacheProgrammedInsertMachine.programmedCache s.cache
      (PrimeSimKeySource.key g pk vote out) out.2.1))
    (s.bad || !(s.cache.lookup (PrimeSimKeySource.key g pk vote out)).isNone)
    (fun j => hw ⟨j.val,by omega⟩)
  change _ = sourceResult slack g pk vote s live out at hout
  refine ⟨charge,?_,he.trans (congrArg (fun cfg => pure (cfg,charge)) hout)⟩
  simpa only [cost,clock,prepareClock,coreClock,CacheProgrammedInsertMachine.cost,Nat.mul_add] using hcharge

/-- The executed cache and sticky flag agree with the original source operation;
ordered-history construction is the next executable stage. -/
theorem source_state (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : PrimeProgrammedInsertSource.State (p:=p) (q:=q))
    (live : PrimeProgrammedInsertSource.Cache (p:=p) (q:=q))
    (out : PrimeProgrammedInsertSource.Draws (q:=q)) :
    let next := (s.program (PrimeSimKeySource.key g pk vote out).1
      (PrimeProgrammedInsertSource.transcript g pk vote out)).2
    let cfg := sourceResult slack g pk vote s live out
    cfg.stk 44 = (ballotCacheBitCodec p q).encode next.cache ∧
    cfg.stk 46 = [next.bad] ∧
    cfg.stk 45 = (ballotCacheBitCodec p q).encode live ∧
    cfg.stk 47 = (ballotStatementBitCodec p q).list.encode s.programmed := by
  cases h : s.cache.lookup (PrimeSimKeySource.key g pk vote out) with
  | none =>
    rw [PrimeProgrammedInsertSource.program_fresh g pk vote out s h]
    simp [sourceResult,CacheProgrammedInsertMachine.programmedCache,h]
    exact ⟨rfl,rfl⟩
  | some value =>
    rw [PrimeProgrammedInsertSource.program_occupied g pk vote out s value h]
    simp [sourceResult,CacheProgrammedInsertMachine.programmedCache,h]
    exact ⟨rfl,rfl⟩

/-- Every scratch word required by the following statement/history constructor
is blank in the actual successor. -/
theorem source_work (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : PrimeProgrammedInsertSource.State (p:=p) (q:=q))
    (live : PrimeProgrammedInsertSource.Cache (p:=p) (q:=q))
    (out : PrimeProgrammedInsertSource.Draws (q:=q)) (j : Fin 7) :
    (sourceResult slack g pk vote s live out).stk ⟨23+j.val,by omega⟩ = [] := by
  fin_cases j <;> rfl

#print axioms charged_source
#print axioms source_state
#print axioms source_work
end ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertMachine
