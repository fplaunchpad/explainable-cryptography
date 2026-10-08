import ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachineRun

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryControls
open PrimeProgrammedHistoryMachine Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
private def w (s : String) : List Bool := s.toList.map (· == '1')

private def emptyWords : Fin 48 → List Bool := ![w "1",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "01",w "1",w "01",w "01",w "101",w "01",w "101",w "01",w "",w "",w "",w "",w "",w "",w "",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "0"]
/-- Independent literal complete-state fixture from the bounded gate. -/
theorem empty_full_state :
    tick^[clock 3 1] (start emptyWords) =
      (⟨none,2,![w "1",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "01",w "1",w "01",w "01",w "101",w "01",w "101",w "01",w "",w "",w "",w "",w "",w "",w "",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "10111111110101100111001111110100111100111011101111010111001111110100111100111101011100111011101"]⟩ : Config) := by
  have he := padded_run 3 ![1,2,2,1] [] emptyWords
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> decide)
    (by intro j; fin_cases j <;> rfl) rfl
  refine he.trans ?_
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl
#print axioms empty_full_state

private def duplicatesWords : Fin 48 → List Bool := ![w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "001",w "01",w "1",w "01",w "101",w "01",w "101",w "01",w "",w "",w "",w "",w "",w "",w "",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "10111111110110010111001111110111111100111101011100111101111110001111110100111100111011101111010111001"]
/-- Independent literal complete-state fixture from the bounded gate. -/
theorem duplicates_full_state :
    tick^[clock 7 101] (start duplicatesWords) =
      (⟨none,2,![w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "001",w "01",w "1",w "01",w "101",w "01",w "101",w "01",w "",w "",w "",w "",w "",w "",w "",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "110011111111011001011100111111011111110011110101110011110111111000111111010011110011101110111101011100111111110110010111001111110111111100111101011100111101111110001111110100111100111011101111010111001"]⟩ : Config) := by
  have he := padded_run 7 ![2,1,4,2] [w "11001111110111111100111101011100111101111110001111110100111100111011101111010111001"] duplicatesWords
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> decide)
    (by intro j; fin_cases j <;> rfl) rfl
  refine he.trans ?_
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl
#print axioms duplicates_full_state

private def count_boundaryWords : Fin 48 → List Bool := ![w "1",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "001",w "01",w "001",w "01",w "101",w "01",w "101",w "01",w "",w "",w "",w "",w "",w "",w "",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "11011111111101100101110011111101111111001111010111001111011111100011111101001111001110111011110101110011111111011001011100111111011111110011110101110011110111111000111111010011110011101110111101011100111111110110010111001111110111111100111101011100111101111110001111110100111100111011101111010111001"]
/-- Independent literal complete-state fixture from the bounded gate. -/
theorem count_boundary_full_state :
    tick^[clock 7 299] (start count_boundaryWords) =
      (⟨none,2,![w "1",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "001",w "01",w "001",w "01",w "101",w "01",w "101",w "01",w "",w "",w "",w "",w "",w "",w "",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "101",w "01",w "11100011111111010101011100111111011111110011110101110011110111111000111111011011110011110111111000111011101111111101100101110011111101111111001111010111001111011111100011111101001111001110111011110101110011111111011001011100111111011111110011110101110011110111111000111111010011110011101110111101011100111111110110010111001111110111111100111101011100111101111110001111110100111100111011101111010111001"]⟩ : Config) := by
  have he := padded_run 7 ![1,4,4,2] [w "11001111110111111100111101011100111101111110001111110100111100111011101111010111001",w "11001111110111111100111101011100111101111110001111110100111100111011101111010111001",w "11001111110111111100111101011100111101111110001111110100111100111011101111010111001"] count_boundaryWords
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> decide)
    (by intro j; fin_cases j <;> rfl) rfl
  refine he.trans ?_
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl
#print axioms count_boundary_full_state

/-- The exact independently expected update differs from chronological append. -/
theorem prepend_not_append : w "1101111111110101001111001111110111111100111101011100111101111110001111111010010111001111101001111100001111101001111101011111111101011011110011111110110001110011110101110111111010011111010011111110110101110011111010011111000111111011011111100000111111110110010111001111110100111100111011101111010111001111110111111100111101011101111101111110001" ≠ w "1101111111110101101111001111111011000111001111010111011111101001111101001111111011010111001111101001111100011111101101111110000011111111011001011100111111010011110011101110111101011100111111011111110011110101110111110111111000111111110101001111001111110111111100111101011100111101111110001111111010010111001111101001111100001111101001111101011" := by decide +kernel

private def omitIncrement (l : Fin size) :=
  if l = 5 then guard (enter (writerLabel 2 3)) else program l
/-- An actual skipped-increment instruction enters a different live slice. -/
theorem skipped_increment_boundary :
    ((TM2ReturnLink.tick omitIncrement)
      (state (some 5) 2 emptyWords (3 : Nat).bits [] [])).l ≠
    (tick (state (some 5) 2 emptyWords (3 : Nat).bits [] [])).l := by decide +kernel
private def corruptFlag (l : Fin size) :=
  if l = 8 then Stmt.push 46 (fun _ => false) (program l) else program l
/-- Actual final-instruction corruption is visible in a retained state field. -/
theorem retained_flag_boundary :
    ((TM2ReturnLink.tick corruptFlag) (state (some 8) 2 emptyWords [] [] [])).stk 46 ≠
    (tick (state (some 8) 2 emptyWords [] [] [])).stk 46 := by decide +kernel
#print axioms prepend_not_append
#print axioms skipped_increment_boundary
#print axioms retained_flag_boundary
end ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryControls
