import ExplainableCrypto.Helios.Computational.PrimeProgramProofSource

namespace ExplainableCrypto.Helios.Computational.PrimeProgramProofSourceControls
open PrimeProgramProofSource
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (Nat.Prime 3) := ⟨by decide⟩
instance : Fact (Nat.Prime 23) := ⟨by decide⟩
instance : Fact (Nat.Prime 11) := ⟨by decide⟩
private def g3 : PrimeGroup 7 3 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (2 : ZMod 7) (by decide : (2 : ZMod 7)^3=1))
private def pk3 : PrimeGroup 7 3 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (4 : ZMod 7) (by decide : (4 : ZMod 7)^3=1))
private def g11 : PrimeGroup 23 11 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (2 : ZMod 23) (by decide : (2 : ZMod 23)^11=1))
private def pk11 : PrimeGroup 23 11 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (4 : ZMod 23) (by decide : (4 : ZMod 23)^11=1))
private def w (s : String) : List Bool := s.toList.map (· == '1')

/-- Independent modular-arithmetic branch fields; includes wrapped subtraction/zero records. -/
theorem wrapped_q3_fields :
    (fun i => (primeGroupCoordinate (groups g3 pk3 true ((1,2),(0,1,1,2)) i)).val) = ![1,4,1,1] ∧
    scalars g3 pk3 true ((1,2),(0,1,1,2)) = ![1,1,2,2] := by
  constructor <;> funext i <;> fin_cases i <;> decide +kernel
/-- Independently encoded nested record, not a flat field list or hash key. -/
theorem wrapped_q3_encoding :
    (ballotProofBitCodec 7 3).encode (proof g3 pk3 true ((1,2),(0,1,1,2))) = w "1100111111110110100111001111110110111100111011101111011111100011111101010111001110111011101110111111110101100111001111110101011100111011101110111011111101011111001111010111001111010111001" := by decide +kernel
#print axioms wrapped_q3_fields
#print axioms wrapped_q3_encoding

/-- Independent modular-arithmetic branch fields; includes wrapped subtraction/zero records. -/
theorem distinct_q11_fields :
    (fun i => (primeGroupCoordinate (groups g11 pk11 true ((3,1),(2,0,4,0)) i)).val) = ![16,3,9,12] ∧
    scalars g11 pk11 true ((3,1),(2,0,4,0)) = ![0,4,2,0] := by
  constructor <;> funext i <;> fin_cases i <;> decide +kernel
/-- Independently encoded nested record, not a flat field list or hash key. -/
theorem distinct_q11_encoding :
    (ballotProofBitCodec 23 11).encode (proof g11 pk11 true ((3,1),(2,0,4,0))) = w "11001111111101001101110011111110101001110011111011011111100000111101011101111111011101110011010111011111100011111111011011011100111111101001011100111110100111110100111110100111110001111111010101110011110101110011010" := by decide +kernel
#print axioms distinct_q11_fields
#print axioms distinct_q11_encoding

/-- The one-branch challenge is q-wrapped c-e, excluding c and natural monus here. -/
theorem wrapped_difference_not_challenge :
    (scalars g3 pk3 true ((1,2),(0,1,1,2)) 2 : ZMod 3) = 2 ∧
    (scalars g3 pk3 true ((1,2),(0,1,1,2)) 2 : ZMod 3) ≠ 0 := by decide +kernel
/-- Swapping zero and one branch records changes this independently fixed proof. -/
theorem branches_not_interchangeable :
    (ballotBranchBitCodec 23 11).encode (proof g11 pk11 true ((3,1),(2,0,4,0))).zero ≠
    (ballotBranchBitCodec 23 11).encode (proof g11 pk11 true ((3,1),(2,0,4,0))).one := by decide +kernel
/-- A sampled zero branch challenge is retained as U(0), not dropped. -/
theorem zero_scalar_has_record :
    scalarEncode (scalars g11 pk11 true ((3,1),(2,0,4,0)) 0) = [false] ∧
    scalarEncode (scalars g11 pk11 true ((3,1),(2,0,4,0)) 0) ≠ [] := by decide +kernel
#print axioms wrapped_difference_not_challenge
#print axioms branches_not_interchangeable
#print axioms zero_scalar_has_record
end ExplainableCrypto.Helios.Computational.PrimeProgramProofSourceControls
