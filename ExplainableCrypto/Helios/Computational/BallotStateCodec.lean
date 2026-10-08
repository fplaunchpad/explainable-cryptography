import ExplainableCrypto.Helios.Computational.BallotCacheCodec
import ExplainableCrypto.Helios.Computational.BallotFiniteProgrammed

/-! Complete finite interpreter states. Histories retain their exact order and
repetitions; the sticky flag and the two distinct caches remain explicit. -/
namespace ExplainableCrypto.Helios.Computational

def ballotBoolBitCodec : BitRecordCodec Bool where
  encode b := [b]
  decode word := match word with | [b] => some b | _ => none
  roundTrip _ := rfl
  exact word b h := by
    split at h
    · cases Option.some.inj h; rfl
    · cases h

variable (p q : Nat) [NeZero p] [NeZero q]

def ballotStatementBitCodec : BitRecordCodec (BallotStatement (PrimeGroup p q)) :=
  (((primeGroupBitCodec p q).pair (primeGroupBitCodec p q)).pair
    ((primeGroupBitCodec p q).pair (primeGroupBitCodec p q))).equiv
    { toFun := fun x => ⟨x.1.1,x.1.2,x.2⟩
      invFun := fun s => ((s.generator,s.publicKey),s.ciphertext)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def ballotLogEntryBitCodec : BitRecordCodec (Unit × BallotForkPoint (PrimeGroup p q)) :=
  (ballotKeyBitCodec p q).equiv
    { toFun := fun key => ((),key)
      invFun := Prod.snd
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨⟨⟩,key⟩; rfl }

def ballotLoggedBitCodec : BitRecordCodec (BallotFiniteLoggedState (ZMod q) (PrimeGroup p q)) :=
  (ballotCacheBitCodec p q).pair (ballotLogEntryBitCodec p q).list

def ballotProgrammedBitCodec :
    BitRecordCodec (BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q)) :=
  ((ballotCacheBitCodec p q).pair
    (ballotBoolBitCodec.pair (ballotStatementBitCodec p q).list)).equiv
    { toFun := fun x => ⟨x.1,x.2.1,x.2.2⟩
      invFun := fun s => (s.cache,s.bad,s.programmed)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Shadow cache, flag and history paired with the separate live cache. -/
def ballotBothCachesBitCodec : BitRecordCodec
    (BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q) ×
      BallotFiniteCache (ZMod q) (PrimeGroup p q)) :=
  (ballotProgrammedBitCodec p q).pair (ballotCacheBitCodec p q)

variable {p q}

theorem ballotLoggedBits_roundTrip (s : BallotFiniteLoggedState (ZMod q) (PrimeGroup p q)) :
    (ballotLoggedBitCodec p q).decode ((ballotLoggedBitCodec p q).encode s) = some s :=
  BitRecordCodec.roundTrip _ _

theorem ballotLoggedBits_exact (word : List Bool)
    (s : BallotFiniteLoggedState (ZMod q) (PrimeGroup p q))
    (h : (ballotLoggedBitCodec p q).decode word = some s) :
    word = (ballotLoggedBitCodec p q).encode s := BitRecordCodec.exact _ _ _ h

theorem ballotProgrammedBits_roundTrip
    (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q)) :
    (ballotProgrammedBitCodec p q).decode ((ballotProgrammedBitCodec p q).encode s) = some s :=
  BitRecordCodec.roundTrip _ _

theorem ballotProgrammedBits_exact (word : List Bool)
    (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (h : (ballotProgrammedBitCodec p q).decode word = some s) :
    word = (ballotProgrammedBitCodec p q).encode s := BitRecordCodec.exact _ _ _ h

theorem ballotBothCachesBits_roundTrip
    (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q) ×
      BallotFiniteCache (ZMod q) (PrimeGroup p q)) :
    (ballotBothCachesBitCodec p q).decode ((ballotBothCachesBitCodec p q).encode s) = some s :=
  BitRecordCodec.roundTrip _ _

theorem ballotBothCachesBits_exact (word : List Bool)
    (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q) ×
      BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (h : (ballotBothCachesBitCodec p q).decode word = some s) :
    word = (ballotBothCachesBitCodec p q).encode s := BitRecordCodec.exact _ _ _ h

/-- Apply the actual sampled-transcript transition to encoded shadow state.
The returned proof remains typed until the ballot/proof codec is assembled. -/
def ballotProgrammedBitsApply (p q : Nat) [NeZero p] [Fact q.Prime]
    (word : List Bool) (stmt : BallotStatement (PrimeGroup p q))
    (t : BallotCommitment (PrimeGroup p q) × ZMod q × BallotResponse (ZMod q)) :
    Option (Proof01 (ZMod q) (PrimeGroup p q) × List Bool) := do
  let s ← (ballotProgrammedBitCodec p q).decode word
  let out := s.program stmt t
  some (out.1,(ballotProgrammedBitCodec p q).encode out.2)

theorem ballotProgrammedBitsApply_encode {p q : Nat} [NeZero p] [Fact q.Prime]
    (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (stmt : BallotStatement (PrimeGroup p q))
    (t : BallotCommitment (PrimeGroup p q) × ZMod q × BallotResponse (ZMod q)) :
    ballotProgrammedBitsApply p q ((ballotProgrammedBitCodec p q).encode s) stmt t =
      some ((s.program stmt t).1,(ballotProgrammedBitCodec p q).encode (s.program stmt t).2) := by
  simp [ballotProgrammedBitsApply,BitRecordCodec.roundTrip]

#print axioms ballotLoggedBits_roundTrip
#print axioms ballotLoggedBits_exact
#print axioms ballotProgrammedBits_roundTrip
#print axioms ballotProgrammedBits_exact
#print axioms ballotBothCachesBits_roundTrip
#print axioms ballotBothCachesBits_exact
#print axioms ballotProgrammedBitsApply_encode
end ExplainableCrypto.Helios.Computational
