import ExplainableCrypto.Helios.Computational.NativeRoundTrip

/-! Full deterministic export/import segments of the native oracle round trip.
Existing memory and stack frames preserve the original three head codes and
all native words outside each routine's fixed workspace. -/
namespace ExplainableCrypto.Helios.Computational.NativeRoundTrip
open Turing OracleComp OracleSpec
open BitTapeCoverage (Cell cellCode readCell cells)
open NativeRoundTripMemory (pack unpack)
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

def exportFrame (before after : Fin 3 → List Cell) : Fin 5 → List Bool :=
  ![cells (before 0),cells (after 0),cells (before 1),cells (before 2),cells (after 2)]
def importFrame (before after : Fin 3 → List Cell) : Fin 5 → List Bool :=
  ![cells (before 0),cells (after 0),cells (before 1),cells (after 1),[]]
def exportInitial (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) :=
  NativeRoundTripMemory.embed (headsCode h) (TM2StackFrame.embed exportLayout
    (NativeQueryExportAdapter.initial (h 1) (after 1)) (exportFrame before after))
def exportResult (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) :=
  NativeRoundTripMemory.embed (headsCode h) (TM2StackFrame.embed exportLayout
    (NativeQueryExportAdapter.result (h 1) (after 1)) (exportFrame before after))
def importInitial (h : Fin 3 → Cell) (before after : Fin 3 → List Cell)
    (reply rawQuery : List Bool) :=
  NativeRoundTripMemory.embed (headsCode h) (TM2StackFrame.embed importLayout
    (NativeAnswerImport.initial (cells (before 2)) reply rawQuery) (importFrame before after))
def importResult (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) (reply : List Bool) :=
  NativeRoundTripMemory.embed (headsCode h) (TM2StackFrame.embed importLayout
    (NativeAnswerImport.result reply) (importFrame before after))

theorem exportInitial_eq (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) :
    exportInitial h before after =
      (⟨some 0,pack (headsCode h) (cellCode (h 1)),words before after⟩ :
        BitOracleMachine.Config 8 4 81) := by
  apply congrArg (fun xs : Fin 8 → List Bool =>
    (⟨some 0,pack (headsCode h) (cellCode (h 1)),xs⟩ : BitOracleMachine.Config 8 4 81))
  funext k; fin_cases k <;> rfl

theorem exportResult_eq (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) :
    exportResult h before after =
      (⟨none,pack (headsCode h) (cellCode (h 1)),
        ![cells (before 0),cells (after 0),cells (before 1),cells (after 1),
          cells (before 2),cells (after 2),NativeQueryExport.wordPrefix (h 1::after 1),[]]⟩ :
        BitOracleMachine.Config 8 4 81) := by
  apply congrArg (fun xs : Fin 8 → List Bool =>
    (⟨none,pack (headsCode h) (cellCode (h 1)),xs⟩ : BitOracleMachine.Config 8 4 81))
  funext k; fin_cases k <;> rfl

theorem importInitial_eq (h : Fin 3 → Cell) (before after : Fin 3 → List Cell)
    (reply rawQuery : List Bool) :
    importInitial h before after reply rawQuery =
      (⟨some 0,pack (headsCode h) (0 : Fin 3),
        ![cells (before 0),cells (after 0),cells (before 1),cells (after 1),
          cells (before 2),reply,rawQuery,[]]⟩ : BitOracleMachine.Config 8 5 81) := by
  apply congrArg (fun xs : Fin 8 → List Bool =>
    (⟨some 0,pack (headsCode h) (0 : Fin 3),xs⟩ : BitOracleMachine.Config 8 5 81))
  funext k; fin_cases k <;> rfl

theorem importResult_eq (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) (reply : List Bool) :
    importResult h before after reply =
      (⟨none,pack (headsCode h) (cellCode reply.head?),
        ![cells (before 0),cells (after 0),cells (before 1),cells (after 1),
          [],cells (reply.tail.map some),[],[]]⟩ : BitOracleMachine.Config 8 5 81) := by
  apply congrArg (fun xs : Fin 8 → List Bool =>
    (⟨none,pack (headsCode h) (cellCode reply.head?),xs⟩ : BitOracleMachine.Config 8 5 81))
  funext k; fin_cases k <;> rfl

theorem export_source_run (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) :
    (TM2ReturnLink.tick exportProgram)^[NativeQueryExportAdapter.clock (h 1) (after 1)]
      (exportInitial h before after) = exportResult h before after := by
  unfold exportProgram exportInitial exportResult
  rw [NativeRoundTripMemory.run,TM2StackFrame.run,NativeQueryExportAdapter.run]

theorem import_source_run (h : Fin 3 → Cell) (before after : Fin 3 → List Cell)
    (reply rawQuery : List Bool) :
    (TM2ReturnLink.tick importProgram)^[NativeAnswerImport.clock (cells (before 2)) reply rawQuery]
      (importInitial h before after reply rawQuery) = importResult h before after reply := by
  unfold importProgram importInitial importResult
  rw [NativeRoundTripMemory.run,TM2StackFrame.run,NativeAnswerImport.run]

theorem export_local_cost (q : Fin 4) : BitOracleMachine.localCost (exportProgram q) ≤ 6 := by
  unfold exportProgram
  rw [NativeRoundTripMemory.local_cost,BitOracleStackFrame.local_cost]
  exact NativeQueryExportAdapter.local_cost q

theorem import_local_cost (q : Fin 5) : BitOracleMachine.localCost (importProgram q) ≤ 5 := by
  unfold importProgram
  rw [NativeRoundTripMemory.local_cost,BitOracleStackFrame.local_cost]
  exact NativeAnswerImport.local_cost q

theorem export_source_charged (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) :
    ∃ charge ≤ NativeQueryExportAdapter.cost (h 1) (after 1),
      BitOracleMachine.run (fun q => .compute (exportProgram q))
        (NativeQueryExportAdapter.clock (h 1) (after 1)) (exportInitial h before after) =
          pure (exportResult h before after,charge) := by
  obtain ⟨charge,hc,he⟩ := BitOracleMachine.compute_run_cost exportProgram 6 export_local_cost
    (NativeQueryExportAdapter.clock (h 1) (after 1)) (exportInitial h before after)
  rw [export_source_run] at he
  exact ⟨charge,hc,he⟩

theorem import_source_charged (h : Fin 3 → Cell) (before after : Fin 3 → List Cell)
    (reply rawQuery : List Bool) :
    ∃ charge ≤ NativeAnswerImport.cost (cells (before 2)) reply rawQuery,
      BitOracleMachine.run (fun q => .compute (importProgram q))
        (NativeAnswerImport.clock (cells (before 2)) reply rawQuery)
        (importInitial h before after reply rawQuery) = pure (importResult h before after reply,charge) := by
  obtain ⟨charge,hc,he⟩ := BitOracleMachine.compute_run_cost importProgram 5 import_local_cost
    (NativeAnswerImport.clock (cells (before 2)) reply rawQuery) (importInitial h before after reply rawQuery)
  rw [import_source_run] at he
  exact ⟨charge,hc,he⟩

private theorem read_code (c : Cell) : readCell (cellCode c) = c := by
  cases c with | none => rfl | some b => cases b <;> rfl

theorem heads_headsCode (h : Fin 3 → Cell) : heads (headsCode h) = h := by
  funext k
  fin_cases k <;> simp [heads,headsCode,read_code]

theorem currentHeads_memory (h : Fin 3 → Cell) : currentHeads (memory h) = h := by
  simp [currentHeads,memory,NativeRoundTripMemory.unpack_pack,heads_headsCode]

theorem nativeState_heads {l : Nat} (q : Fin l) (h : Fin 3 → Cell)
    (before after : Fin 3 → List Cell) : NativeOracleTape.heads (nativeState q h before after) = h := by
  funext k
  fin_cases k <;> rfl

/-- The resident finite representation relation at native continuation entries.
Its witnesses are actual finite cells, rather than a runtime decoder assumption. -/
def Represents {l : Nat} (resident : Config l) (native : NativeOracleTape.Config l) : Prop :=
  ∃ (q : Fin l) (h : Fin 3 → Cell) (before after : Fin 3 → List Cell),
    resident = initial q h before after ∧ native = nativeState q h before after

theorem initial_represents {l : Nat} (q : Fin l) (h : Fin 3 → Cell)
    (before after : Fin 3 → List Cell) :
    Represents (initial q h before after) (nativeState q h before after) :=
  ⟨q,h,before,after,rfl,rfl⟩

theorem result_initial {l : Nat} (next : Fin l) (h : Fin 3 → Cell)
    (before after : Fin 3 → List Cell) (reply : List Bool) :
    result next h before after reply =
      initial next ![h 0,h 1,reply.head?]
        ![before 0,before 1,[]] ![after 0,after 1,reply.tail.map some] := by
  rfl

/-- The imported representation denotes the ordinary complete native reply tape,
including an empty word or a false first bit. -/
theorem reply_tape (reply : List Bool) :
    BitTapeCoverage.tape (l := 0) ⟨none,reply.head?,[],reply.tail.map some⟩ =
      OracleTapeOutput.wordTape reply := by
  cases reply with
  | nil => rfl
  | cons bit rest => rfl

theorem result_represents {l : Nat} (next : Fin l) (h : Fin 3 → Cell)
    (before after : Fin 3 → List Cell) (reply : List Bool) :
    Represents (result next h before after reply)
      (⟨some next,(nativeState next h before after).work,
        (nativeState next h before after).query,OracleTapeOutput.wordTape reply⟩ :
        NativeOracleTape.Config l) := by
  refine ⟨next,![h 0,h 1,reply.head?],![before 0,before 1,[]],
    ![after 0,after 1,reply.tail.map some],result_initial next h before after reply,?_⟩
  change (⟨some next,_,_,OracleTapeOutput.wordTape reply⟩ : NativeOracleTape.Config l) =
    ⟨some next,_,_,BitTapeCoverage.tape (l := 0) ⟨none,reply.head?,[],reply.tail.map some⟩⟩
  rw [reply_tape]
  rfl

end ExplainableCrypto.Helios.Computational.NativeRoundTrip
