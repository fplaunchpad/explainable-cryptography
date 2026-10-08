import ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertMachine
import ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertInputMachineRun

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

/-- Exact live handoff from executed copy/clear to the existing insertion code.
Only scratch and the singleton flag are local premises; source_return derives them. -/
theorem prep_return (old : Fin 48 → List Bool) (bad : Bool)
    (hwork : ∀ j : Fin 6, old ⟨23+j.val,by omega⟩ = []) (hbad : old 46 = [bad]) :
    BitOracleReturnLink.embed prefixLabel (some (coreLabel 0))
      (PrimeProgrammedInsertInputMachine.result old) =
    BitOracleReturnLink.embed coreLabel none
      (BitOracleStackFrame.embed coreLayout
        (CacheProgrammedInsertMachine.start (old 44) (old 10) (old 43) (old 45) (old 47) bad)
        (frame old)) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k
  fin_cases k <;> first | rfl | exact hwork 0 | exact hwork 1 | exact hwork 2 | exact hwork 3 | exact hwork 4 | exact hwork 5 | exact hbad

/-- No caller presentation is assumed: all six blank words and the old flag
are those of the actual typed state-extraction successor. -/
theorem source_return {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    let old := (PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out).stk
    BitOracleReturnLink.embed prefixLabel (some (coreLabel 0))
      (PrimeProgrammedInsertInputMachine.result old) =
    BitOracleReturnLink.embed coreLabel none
      (BitOracleStackFrame.embed coreLayout
        (CacheProgrammedInsertMachine.start ((ballotCacheBitCodec p q).encode s.cache)
          ((primeScalarBitCodec q).encode out.2.1)
          ((ballotKeyBitCodec p q).encode (PrimeSimKeySource.key g pk vote out))
          ((ballotCacheBitCodec p q).encode live)
          ((ballotStatementBitCodec p q).list.encode s.programmed) s.bad)
        (frame old)) := by
  apply prep_return _ s.bad
  · intro j
    exact PrimeProgrammedInsertSource.source_work slack g pk vote s live out ⟨j.val,by omega⟩
  · rfl

/-- The complete framed insertion result changes only the shadow cache and
sticky flag. Live cache, exact history, challenge, key and arbitrary frame persist. -/
theorem core_result (old : Fin 48 → List Bool) (cache : List Bool) (bad : Bool)
    (hwork : ∀ j : Fin 6, old ⟨23+j.val,by omega⟩ = []) :
    BitOracleReturnLink.embed coreLabel none
      (BitOracleStackFrame.embed coreLayout
        (CacheProgrammedInsertMachine.result cache (old 10) (old 43) (old 45) (old 47) bad)
        (frame old)) =
      (⟨none,2,Function.update (Function.update old 44 cache) 46 [bad]⟩ : Config) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k
  fin_cases k <;> first | rfl | exact (hwork 0).symm | exact (hwork 1).symm |
    exact (hwork 2).symm | exact (hwork 3).symm | exact (hwork 4).symm | exact (hwork 5).symm

#print axioms prep_return
#print axioms source_return
#print axioms core_result
end ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertMachine
open OracleComp OracleSpec BitOracleMachine
set_option maxHeartbeats 400000
set_option maxRecDepth 65536
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
attribute [local irreducible] BitOracleMachine.run

/-- Link the actual cache preparation to a halting insertion run. The source
specialization below derives the boundary and insertion hypotheses. -/
theorem charged_link (old : Fin 48 → List Bool) (N T B : Nat)
    (h23 : old 23 = []) (h24 : old 24 = []) (hcache : (old 44).length ≤ N)
    (initial final : CacheProgrammedInsertMachine.Config) (saved : Fin 36 → List Bool)
    (hboundary : BitOracleReturnLink.embed prefixLabel (some (coreLabel 0))
      (PrimeProgrammedInsertInputMachine.result old) =
      BitOracleReturnLink.embed coreLabel none (BitOracleStackFrame.embed coreLayout initial saved))
    (hh : final.l = none)
    (hc : ∃ charge ≤ B, BitOracleMachine.run CacheProgrammedInsertMachine.code T initial =
      pure (final,charge)) :
    ∃ charge ≤ 32*(3*N+4)+B,
      BitOracleMachine.run code ((3*N+4)+T) (start old) =
        pure (BitOracleReturnLink.embed coreLabel none
          (BitOracleStackFrame.embed coreLayout final saved),charge) := by
  obtain ⟨c,hc,hr⟩ := hc
  obtain ⟨a,ha,hp⟩ := PrimeProgrammedInsertInputMachine.charged_bounded old N h23 h24 hcache
  have ht : BitOracleMachine.run code T
      (BitOracleReturnLink.embed prefixLabel (some (coreLabel 0))
        (PrimeProgrammedInsertInputMachine.result old)) =
      pure (BitOracleReturnLink.embed coreLabel none
        (BitOracleStackFrame.embed coreLayout final saved),c) := by
    rw [hboundary,BitOracleReturnLink.rename_run _ _ _ core_code]
    change (fun out => (BitOracleReturnLink.embed coreLabel none out.1,out.2)) <$>
      BitOracleMachine.run (BitOracleStackFrame.code coreLayout CacheProgrammedInsertMachine.code)
        T (BitOracleStackFrame.embed coreLayout initial saved) = _
    rw [BitOracleStackFrame.run,hr,map_pure,map_pure]
  have hhalt : ∀ out ∈ support (BitOracleMachine.run PrimeProgrammedInsertInputMachine.code
      (3*N+4) (PrimeProgrammedInsertInputMachine.start old)), out.1.l = none := by
    rw [hp]
    intro out ho
    rw [eq_of_mem_support_pure _ ho]
    rfl
  have htail : ∀ out ∈ support (BitOracleMachine.run PrimeProgrammedInsertInputMachine.code
      (3*N+4) (PrimeProgrammedInsertInputMachine.start old)),
      ∀ last ∈ support (BitOracleMachine.run code T
        (BitOracleReturnLink.embed prefixLabel (some (coreLabel 0)) out.1)), last.1.l = none := by
    rw [hp]
    intro out ho
    rw [eq_of_mem_support_pure _ ho,ht]
    intro last hl
    rw [eq_of_mem_support_pure _ hl]
    change final.l.elim none (some ∘ coreLabel) = none
    rw [hh]
    rfl
  refine ⟨a+c,Nat.add_le_add ha hc,?_⟩
  change BitOracleMachine.run code _ (BitOracleReturnLink.embed prefixLabel _ _) = _
  rw [BitOracleReturnLink.run _ _ _ _ prefix_code _ _ _ hhalt htail,hp]
  simp only [pure_bind,ht]

#print axioms charged_link
end ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertMachine
