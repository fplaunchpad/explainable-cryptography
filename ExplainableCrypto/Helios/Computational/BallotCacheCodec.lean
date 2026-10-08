import ExplainableCrypto.Helios.Computational.BitRecordCodec
import ExplainableCrypto.Helios.Computational.PrimeGroupCodec
import ExplainableCrypto.Helios.Computational.BallotKeyRecord

/-! Complete full-key and ordered finite-cache bit records. Duplicate keys
reject; cache misses remain distinct from malformed records. -/
namespace ExplainableCrypto.Helios.Computational
variable (p q : Nat) [NeZero p] [NeZero q]

def primeGroupBitCodec : BitRecordCodec (PrimeGroup p q) where
  encode := primeGroupEncode
  decode := primeGroupDecode p q
  roundTrip := primeGroupDecode_encode
  exact := primeGroupDecode_exact

def primeScalarBitCodec : BitRecordCodec (ZMod q) where
  encode := scalarEncode
  decode := scalarDecode q
  roundTrip := scalarDecode_encode
  exact := scalarDecode_exact

def ballotKeyBitCodec : BitRecordCodec (BallotForkPoint (PrimeGroup p q)) where
  encode key := (primeGroupBitCodec p q).list.encode (ballotKeyRecord key)
  decode word := do
    let fields ← (primeGroupBitCodec p q).list.decode word
    ballotKeyOfRecord fields
  roundTrip key := by
    rw [BitRecordCodec.roundTrip]
    exact ballotKeyOfRecord_roundTrip key
  exact word key h := by
    cases hf : (primeGroupBitCodec p q).list.decode word with
    | none => simp [hf] at h
    | some fields =>
      simp only [hf] at h
      rw [BitRecordCodec.exact _ word fields hf,ballotKeyOfRecord_exact fields key h]

abbrev PrimeCacheEntry := Σ _ : BallotForkPoint (PrimeGroup p q), ZMod q

def ballotCacheEntryBitCodec : BitRecordCodec (PrimeCacheEntry p q) :=
  ((ballotKeyBitCodec p q).pair (primeScalarBitCodec q)).equiv
    { toFun := fun x => ⟨x.1,x.2⟩
      invFun := fun x => (x.1,x.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private instance cacheEntriesNodup (es : List (PrimeCacheEntry p q)) :
    Decidable es.NodupKeys := inferInstanceAs (Decidable es.keys.Nodup)

def ballotCacheBitCodec : BitRecordCodec (BallotFiniteCache (ZMod q) (PrimeGroup p q)) :=
  (((ballotCacheEntryBitCodec p q).list).subtype List.NodupKeys).equiv
    { toFun := fun x => ⟨x.val,x.property⟩
      invFun := fun x => ⟨x.entries,x.nodupKeys⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

variable {p q}

theorem ballotKeyBits_roundTrip (key : BallotForkPoint (PrimeGroup p q)) :
    (ballotKeyBitCodec p q).decode ((ballotKeyBitCodec p q).encode key) = some key :=
  BitRecordCodec.roundTrip _ _

theorem ballotKeyBits_exact (word : List Bool) (key : BallotForkPoint (PrimeGroup p q))
    (h : (ballotKeyBitCodec p q).decode word = some key) :
    word = (ballotKeyBitCodec p q).encode key := BitRecordCodec.exact _ _ _ h

theorem ballotCacheBits_roundTrip (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q)) :
    (ballotCacheBitCodec p q).decode ((ballotCacheBitCodec p q).encode cache) = some cache :=
  BitRecordCodec.roundTrip _ _

theorem ballotCacheBits_exact (word : List Bool)
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (h : (ballotCacheBitCodec p q).decode word = some cache) :
    word = (ballotCacheBitCodec p q).encode cache := BitRecordCodec.exact _ _ _ h

/-- Complete parsing retains the actual entry order as well as each key/value. -/
theorem ballotCacheBits_injective :
    Function.Injective (ballotCacheBitCodec p q).encode := BitRecordCodec.injective _

/-- Neither agreeing nor disagreeing duplicate keys are silently deduplicated. -/
theorem ballotCacheBits_duplicate (es : List (PrimeCacheEntry p q)) (h : ¬es.NodupKeys) :
    (ballotCacheBitCodec p q).decode ((ballotCacheEntryBitCodec p q).list.encode es) = none := by
  simp [ballotCacheBitCodec,BitRecordCodec.equiv,BitRecordCodec.subtype,
    BitRecordCodec.roundTrip,h]

/-- None is malformed input; some none is a valid cache miss. -/
def ballotCacheBitsLookup (p q : Nat) [NeZero p] [NeZero q]
    (cacheWord keyWord : List Bool) : Option (Option (ZMod q)) := do
  let cache ← (ballotCacheBitCodec p q).decode cacheWord
  let key ← (ballotKeyBitCodec p q).decode keyWord
  some (cache.lookup key)

theorem ballotCacheBitsLookup_encode (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) :
    ballotCacheBitsLookup p q ((ballotCacheBitCodec p q).encode cache)
      ((ballotKeyBitCodec p q).encode key) = some (cache.lookup key) := by
  simp [ballotCacheBitsLookup,BitRecordCodec.roundTrip]

/-- Updating encoded state uses the same finite insertion as the source cache. -/
def ballotCacheBitsInsert (p q : Nat) [NeZero p] [NeZero q]
    (cacheWord keyWord answerWord : List Bool) : Option (List Bool) := do
  let cache ← (ballotCacheBitCodec p q).decode cacheWord
  let key ← (ballotKeyBitCodec p q).decode keyWord
  let answer ← (primeScalarBitCodec q).decode answerWord
  some ((ballotCacheBitCodec p q).encode (cache.insert key answer))

theorem ballotCacheBitsInsert_encode (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (answer : ZMod q) :
    ballotCacheBitsInsert p q ((ballotCacheBitCodec p q).encode cache)
      ((ballotKeyBitCodec p q).encode key) ((primeScalarBitCodec q).encode answer) =
      some ((ballotCacheBitCodec p q).encode (cache.insert key answer)) := by
  simp [ballotCacheBitsInsert,BitRecordCodec.roundTrip]

#print axioms ballotKeyBits_roundTrip
#print axioms ballotKeyBits_exact
#print axioms ballotCacheBits_roundTrip
#print axioms ballotCacheBits_exact
#print axioms ballotCacheBits_injective
#print axioms ballotCacheBits_duplicate
#print axioms ballotCacheBitsLookup_encode
#print axioms ballotCacheBitsInsert_encode
end ExplainableCrypto.Helios.Computational
