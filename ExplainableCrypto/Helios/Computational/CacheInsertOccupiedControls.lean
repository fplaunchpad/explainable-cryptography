import ExplainableCrypto.Helios.Computational.CacheInsertOccupiedRun

namespace ExplainableCrypto.Helios.Computational.CacheInsertOccupiedControls
open Turing.TM2 CacheInsertMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

/-- This actual instruction only changes the return flag; it does not clear hit residue. -/
theorem occupied_boundary :
    tick (state (some .lookupDone) [true,false] [false,true] [] [] [] [true]
      [false] [true,true] [true,false,true] (some true)) =
    state none [true,false] [false,true] [] [] [] [true]
      [false] [true,true] [true,false,true] (some false) := rfl

/-- Literal complete-state boundary excludes the tempting fresh-branch cleanup claim. -/
theorem occupied_boundary_not_clean :
    tick (state (some .lookupDone) [true,false] [false,true] [] [] [] [true]
      [false] [true,true] [true,false,true] (some true)) ≠
    state none [true,false] [] [] [] [] [] [] [true,true] [true,false,true] (some false) := by
  intro h
  have he := congrArg (fun c : Config => c.stk outer) h
  cases he

/-- A concrete canonical occupied cache reaches the nonempty counter state;
its prior answer 5 and proposed answer 7 are independently distinct. -/
theorem canonical_occupied_counter :
    ∃ fuel ≤ cost 23 11 BallotCacheCodecControls.cache.entries.length
      ((ballotCacheBitCodec 23 11).encode BallotCacheCodecControls.cache).length,
      let cfg := tick^[fuel]
        (start ((ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.otherKey)
          ((primeScalarBitCodec 11).encode 7)
          ((ballotCacheBitCodec 23 11).encode BallotCacheCodecControls.cache))
      cfg.l = none ∧ cfg.var = some false ∧ cfg.stk outer ≠ [] :=
  occupied_counter_not_empty BallotCacheCodecControls.cache BallotCacheCodecControls.otherKey 7 5 (by decide)

#print axioms occupied_boundary
#print axioms occupied_boundary_not_clean
#print axioms canonical_occupied_counter
end ExplainableCrypto.Helios.Computational.CacheInsertOccupiedControls
