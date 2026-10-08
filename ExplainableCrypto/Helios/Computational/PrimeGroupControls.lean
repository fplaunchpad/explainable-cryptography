import ExplainableCrypto.Helios.Computational.PrimeGroupCodec

/-! Independent public-coordinate, identity and malformed-record controls. -/
namespace ExplainableCrypto.Helios.Computational.PrimeGroupControls
instance : Fact (Nat.Prime 23) := ⟨by decide⟩
instance : Fact (Nat.Prime 11) := ⟨by decide⟩

def generator : PrimeGroup 23 11 :=
  Additive.ofMul (rootsOfUnity.mkOfPowEq (2 : ZMod 23) (by decide : (2 : ZMod 23)^11 = 1))

def publicKey : PrimeGroup 23 11 := (3 : ZMod 11) • generator

/-- This is an actual nontrivial prime-order group, not a vacuous parameter instance. -/
theorem literal_group : primeGroupCoordinate generator = 2 ∧
    Nat.card (PrimeGroup 23 11) = 11 ∧
    Function.Injective (fun r : ZMod 11 => r • generator) := by
  refine ⟨rfl,primeGroup_card generator (by decide),primeGroup_generator_injective generator (by decide)⟩

/-- Public coordinates agree with the independently computed ElGamal example. -/
theorem literal_encryption :
    primeGroupCoordinate publicKey = 8 ∧
    (primeGroupCoordinate (encryptWith generator publicKey (4 : ZMod 11) 1).1,
      primeGroupCoordinate (encryptWith generator publicKey (4 : ZMod 11) 1).2) = (16,4) ∧
    primeGroupCoordinate (-generator) = 12 := by decide

/-- Identity remains a valid record, while the generator uses coordinate two,
not its discrete-log index one. -/
theorem literal_records :
    primeGroupDecode 23 11 [true,false,true] = some 0 ∧
    primeGroupEncode generator = [true,true,false,false,true] ∧
    primeGroupDecode 23 11 [true,true,false,false,true] = some generator := by decide

/-- Zero, a non-subgroup unit, an out-of-range alias and a trailing bit all reject. -/
theorem malformed_records :
    primeGroupDecode 23 11 (uniformNatEncode 0) = none ∧
    primeGroupDecode 23 11 (uniformNatEncode 22) = none ∧
    primeGroupDecode 23 11 (uniformNatEncode 24) = none ∧
    primeGroupDecode 23 11 [true,false,true,false] = none := by decide

#print axioms literal_group
#print axioms literal_encryption
#print axioms literal_records
#print axioms malformed_records
end ExplainableCrypto.Helios.Computational.PrimeGroupControls
