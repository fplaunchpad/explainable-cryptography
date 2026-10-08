import ExplainableCrypto.Helios.Computational.NativeRoundTripExecution
import ExplainableCrypto.Helios.Computational.NativeRoundTripBounds

namespace ExplainableCrypto.Helios.Computational.NativeRoundTrip
open Turing OracleComp OracleSpec
open BitTapeCoverage (Cell cells)
set_option maxRecDepth 32768
set_option maxHeartbeats 900000
variable {l : Nat}

/-- Full execution factors into its actual single event and actual reply
continuation. Prefix fuel/charge are derived from the original reached state. -/
theorem execution_decomposition (p : NativeOracleTape.Code l) (q next : Fin l)
    (kind : OracleTapeDispatch.Kind) (h : Fin 3 → Cell) (before after : Fin 3 → List Cell)
    (limit : Nat) (hc : p q h = .oracle kind next) :
    ∃ fuel, importClock h before after (limit+1)+2 ≤ fuel ∧
      ∃ charge ≤ 4+6*exportClock h after,
        boundedExecute p q h before after limit = (do
          let reply ← boundedCall limit kind (queryWord h after)
          let last ← simulateQ (BitOracleLoopBounded.adapter limit)
            (NativeReturnObservation.run atNative (code p) fuel
              (replyState next (kindIndex kind) h before after reply))
          pure (last.1,charge+eventCost kind (queryWord h after) (cells (after 2)) reply+last.2)) := by
  obtain ⟨used,hu,charge,hcharge,hr⟩ := export_prefix p next (kindIndex kind) h before after
  let fuel := callFuel h before after limit-used-1
  have hf : importClock h before after (limit+1)+2 ≤ fuel := by
    dsimp [fuel,callFuel]
    omega
  have he : callFuel h before after limit = used+(fuel+1) := by
    dsimp [fuel,callFuel]
    omega
  refine ⟨fuel,hf,2+charge,by omega,?_⟩
  unfold boundedExecute execute
  rw [entry_step p q next kind h before after hc]
  simp only [pure_bind]
  rw [he,NativeReturnObservation.run_add,hr]
  simp only [pure_bind]
  rw [NativeReturnObservation.run_succ_unstopped _ _ _ _
    (show NativeReturnObservation.stopped atNative (oracleState next (kindIndex kind) h before after) = false
      from atNative_block next (kindIndex kind) 5),oracle_step]
  simp only [pure_bind,bind_assoc,simulateQ_bind,simulateQ_pure]
  unfold boundedCall
  apply bind_congr
  intro reply
  apply bind_congr
  intro last
  simp [Nat.add_assoc]

/-- The complete observed event tree returns the exact resident successor for
all allowed replies, including empty hashes and either coin value. -/
theorem execution_correspondence (p : NativeOracleTape.Code l) (q next : Fin l)
    (kind : OracleTapeDispatch.Kind) (h : Fin 3 → Cell) (before after : Fin 3 → List Cell)
    (limit : Nat) (hc : p q h = .oracle kind next) :
    Prod.fst <$> boundedExecute p q h before after limit =
      (result next h before after) <$> boundedCall limit kind (queryWord h after) := by
  obtain ⟨fuel,hfuel,charge,_,he⟩ := execution_decomposition p q next kind h before after limit hc
  rw [he]
  simp only [map_bind,map_pure]
  rw [map_eq_bind_pure_comp]
  apply bind_congr_of_forall_mem_support
  intro reply hr
  obtain ⟨cost,_,hpost⟩ := suffix p next (kindIndex kind) h before after reply
    (limit+1) fuel (boundedCall_length limit kind (queryWord h after) reply hr) hfuel
  rw [hpost]
  simp [simulateQ_pure]

/-- A common exact event tree connects actual native and represented successor
states. The representation is established at every leaf, not assumed. -/
theorem native_correspondence (p : NativeOracleTape.Code l) (q next : Fin l)
    (kind : OracleTapeDispatch.Kind) (h : Fin 3 → Cell) (before after : Fin 3 → List Cell)
    (limit : Nat) (hc : p q h = .oracle kind next) :
    ∃ joint : OracleComp (BitOracleLoopBounded.spec limit) (Config l × NativeOracleTape.Config l),
      Prod.fst <$> joint = Prod.fst <$> boundedExecute p q h before after limit ∧
      Prod.snd <$> joint = simulateQ (BitOracleLoopBounded.adapter limit)
        (NativeOracleTape.step p (nativeState q h before after)) ∧
      ∀ out ∈ support joint, Represents out.1 out.2 := by
  let joint := (fun reply => (result next h before after reply,nativeSuccessor next h before after reply)) <$>
    boundedCall limit kind (queryWord h after)
  refine ⟨joint,?_,?_,?_⟩
  · rw [execution_correspondence p q next kind h before after limit hc]
    simp [joint,Functor.map_map]
  · rw [native_call p q next kind h before after hc]
    simp only [joint,boundedCall,Function.comp_def,simulateQ_bind,simulateQ_pure,
      map_eq_bind_pure_comp,bind_assoc,pure_bind]
  · intro out ho
    have hm : ∃ reply, reply ∈ support (boundedCall limit kind (queryWord h after)) ∧
        (result next h before after reply,nativeSuccessor next h before after reply) = out := by
      simpa [joint] using ho
    obtain ⟨reply,_,rfl⟩ := hm
    exact result_represents_successor next h before after reply

end ExplainableCrypto.Helios.Computational.NativeRoundTrip
