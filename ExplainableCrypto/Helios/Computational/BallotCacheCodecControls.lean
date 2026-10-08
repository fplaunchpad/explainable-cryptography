import ExplainableCrypto.Helios.Computational.BallotCacheBitSize

/-! Literal independent framing and complete-key/cache controls. -/
namespace ExplainableCrypto.Helios.Computational.BallotCacheCodecControls
instance : Fact (Nat.Prime 23) := ⟨by decide⟩
instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private def coordinate (n : Nat) (h : (n : ZMod 23)^11 = 1) : PrimeGroup 23 11 :=
  Additive.ofMul (rootsOfUnity.mkOfPowEq (n : ZMod 23) h)

def key : BallotForkPoint (PrimeGroup 23 11) :=
  (⟨coordinate 1 (by decide),coordinate 2 (by decide),
    coordinate 3 (by decide),coordinate 4 (by decide)⟩,
   (coordinate 6 (by decide),coordinate 8 (by decide)),
   (coordinate 9 (by decide),coordinate 12 (by decide)))

def otherKey : BallotForkPoint (PrimeGroup 23 11) :=
  ({key.1 with generator := key.1.publicKey, publicKey := key.1.generator},key.2)

def cache : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11) :=
  ((∅ : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11)).insert key 3).insert otherKey 5

theorem literal_fields : bitFieldsEncode [[true],[false]] =
    [true,true,false,false,true,true,false,true,true,true,false,true,false] ∧
    bitFieldsDecode [false] = some [] := by decide

theorem literal_full_key : (ballotKeyRecord key).map primeGroupCoordinate =
    [1,2,3,4,6,8,9,12] ∧
    (ballotKeyBitCodec 23 11).encode key ≠ (ballotKeyBitCodec 23 11).encode otherKey := by
  constructor
  · decide
  · exact fun h => (by decide : key ≠ otherKey) (BitRecordCodec.injective _ h)

theorem literal_lookup :
    ballotCacheBitsLookup 23 11 ((ballotCacheBitCodec 23 11).encode cache)
      ((ballotKeyBitCodec 23 11).encode key) = some (some 3) ∧
    ballotCacheBitsLookup 23 11 ((ballotCacheBitCodec 23 11).encode cache)
      ((ballotKeyBitCodec 23 11).encode otherKey) = some (some 5) ∧
    ballotCacheBitsLookup 23 11 ((ballotCacheBitCodec 23 11).encode ∅)
      ((ballotKeyBitCodec 23 11).encode key) = some none := by
  simp only [ballotCacheBitsLookup_encode]
  decide

/-- Duplicate keys reject even when both scalar answers agree. -/
theorem duplicate_rejection (answer : ZMod 11) :
    (ballotCacheBitCodec 23 11).decode
      ((ballotCacheEntryBitCodec 23 11).list.encode [⟨key,answer⟩,⟨key,answer⟩]) = none := by
  apply ballotCacheBits_duplicate
  simp [List.NodupKeys,List.keys]

/-- The encoded representation preserves entry order, not just lookup results. -/
theorem entry_order_preserved :
    (ballotCacheBitCodec 23 11).encode cache ≠
      (ballotCacheBitCodec 23 11).encode
        (((∅ : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11)).insert otherKey 5).insert key 3) := by
  intro h
  have he := ballotCacheBits_injective h
  have hl := congrArg AList.entries he
  have hn : cache.entries ≠
      (((∅ : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11)).insert otherKey 5).insert key 3).entries := by decide
  exact hn hl

/-- Trailing data is not silently discarded, even after the empty cache. -/
theorem trailing_rejection : (ballotCacheBitCodec 23 11).decode [false,false] = none := by decide

#print axioms literal_fields
#print axioms literal_full_key
#print axioms literal_lookup
#print axioms duplicate_rejection
#print axioms entry_order_preserved
#print axioms trailing_rejection
end ExplainableCrypto.Helios.Computational.BallotCacheCodecControls
