import ExplainableCrypto.Helios.Computational.PrimeSimKeySource

/-! Independently calculated coordinate and byte fixtures. These test source
interpretation and the established codec, not serialization execution. -/
namespace ExplainableCrypto.Helios.Computational.PrimeSimKeySourceControls
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (Nat.Prime 3) := ⟨by decide⟩
instance : Fact (Nat.Prime 23) := ⟨by decide⟩
instance : Fact (Nat.Prime 11) := ⟨by decide⟩
private def g3 : PrimeGroup 7 3 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (2 : ZMod 7) (by decide : (2 : ZMod 7)^3 = 1))
private def pk3 : PrimeGroup 7 3 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (4 : ZMod 7) (by decide : (4 : ZMod 7)^3 = 1))
private def g11 : PrimeGroup 23 11 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (2 : ZMod 23) (by decide : (2 : ZMod 23)^11 = 1))
private def pk11 : PrimeGroup 23 11 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (4 : ZMod 23) (by decide : (4 : ZMod 23)^11 = 1))

theorem true_q3_digits :
    PrimeSimKeySource.ports.map
      (PrimeSimAllCommitCaller.sourceResult 0 g3 pk3 true [true,false,true] ((1,2),(0,1,1,2))).stk =
      [[false,true],[false,false,true],[false,true],[true],[true],[false,false,true],[true],[true]] := by decide +kernel

theorem true_q3_encoding :
    (ballotKeyBitCodec 7 3).encode (PrimeSimKeySource.key g3 pk3 true ((1,2),(0,1,1,2))) =
      [true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true] := by decide +kernel

#print axioms true_q3_digits
#print axioms true_q3_encoding

theorem false_q3_digits :
    PrimeSimKeySource.ports.map
      (PrimeSimAllCommitCaller.sourceResult 0 g3 pk3 false [true,false,true] ((1,2),(0,1,2,2))).stk =
      [[false,true],[false,false,true],[false,true],[false,false,true],[false,true],[false,false,true],[true],[false,false,true]] := by decide +kernel

theorem false_q3_encoding :
    (ballotKeyBitCodec 7 3).encode (PrimeSimKeySource.key g3 pk3 false ((1,2),(0,1,2,2))) =
      [true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true] := by decide +kernel

#print axioms false_q3_digits
#print axioms false_q3_encoding

theorem distinct_q11_digits :
    PrimeSimKeySource.ports.map
      (PrimeSimAllCommitCaller.sourceResult 0 g11 pk11 true [true,false,true] ((3,1),(2,0,4,0))).stk =
      [[false,true],[false,false,true],[false,false,false,true],[true,false,true,true],[false,false,false,false,true],[true,true],[true,false,false,true],[false,false,true,true]] := by decide +kernel

theorem distinct_q11_encoding :
    (ballotKeyBitCodec 23 11).encode (PrimeSimKeySource.key g11 pk11 true ((3,1),(2,0,4,0))) =
      [true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,false,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,true,false,true,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,false,false,true,true] := by decide +kernel

#print axioms distinct_q11_digits
#print axioms distinct_q11_encoding

/-- This independent malformed or reordered byte candidate differs from the exact key. -/
theorem omitted_count :
    (ballotKeyBitCodec 23 11).encode
      (PrimeSimKeySource.key g11 pk11 true ((3,1),(2,0,4,0))) ≠
      [true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,false,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,true,false,true,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,false,false,true,true] := by
  rw [distinct_q11_encoding]
  decide +kernel
#print axioms omitted_count

/-- This independent malformed or reordered byte candidate differs from the exact key. -/
theorem swapped_generator_key :
    (ballotKeyBitCodec 23 11).encode
      (PrimeSimKeySource.key g11 pk11 true ((3,1),(2,0,4,0))) ≠
      [true,true,true,true,false,false,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,false,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,true,false,true,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,false,false,true,true] := by
  rw [distinct_q11_encoding]
  decide +kernel
#print axioms swapped_generator_key

/-- This independent malformed or reordered byte candidate differs from the exact key. -/
theorem omitted_scalar_prefix :
    (ballotKeyBitCodec 23 11).encode
      (PrimeSimKeySource.key g11 pk11 true ((3,1),(2,0,4,0))) ≠
      [true,true,true,true,false,false,false,false,true,true,true,false,false,true,false,true,true,true,false,true,true,false,false,true,true,true,true,false,false,false,true,false,false,false,true,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,false,true,false,false,false,false,true,true,true,false,false,true,true,true,true,true,true,false,false,false,true,true,false,false,true,true,true,true,false,false,false,true,false,false,true,true] := by
  rw [distinct_q11_encoding]
  decide +kernel
#print axioms omitted_scalar_prefix

end ExplainableCrypto.Helios.Computational.PrimeSimKeySourceControls
