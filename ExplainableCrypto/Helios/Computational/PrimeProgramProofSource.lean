import ExplainableCrypto.Helios.Computational.PrimeProgramCallerSource
import ExplainableCrypto.Helios.Computational.BallotOutputBitSize

/-! Exact first returned proof and its operands in the executed resident state.
No runtime serializer or new protocol correctness assumption is introduced. -/
namespace ExplainableCrypto.Helios.Computational.PrimeProgramProofSource
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
abbrev State := BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q)
abbrev Cache := BallotFiniteCache (ZMod q) (PrimeGroup p q)
abbrev Draws := (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)

def proof (g pk : PrimeGroup p q) (vote : Bool) (out : Draws (q:=q)) :
    Proof01 (ZMod q) (PrimeGroup p q) :=
  ballotTranscriptProof (PrimeSimKeySource.key g pk vote out).2 out.2.1
    (out.2.2.1,out.2.2.2.1,out.2.2.2.2)

/-- Both fresh and occupied branches return the same sampled transcript proof. -/
theorem program_return (g pk : PrimeGroup p q) (vote : Bool) (out : Draws (q:=q))
    (s : State (p:=p) (q:=q)) :
    (s.program (PrimeSimKeySource.key g pk vote out).1
      (PrimeProgrammedInsertSource.transcript g pk vote out)).1 = proof g pk vote out := by
  unfold BallotFiniteProgrammedState.program
  split <;> rfl

def groupPort : Fin 4 → Fin 48 := ![3,38,40,42]
def scalarPort : Fin 4 → Fin 48 := ![11,12,1,7]
def groups (g pk : PrimeGroup p q) (vote : Bool) (out : Draws (q:=q)) : Fin 4 → PrimeGroup p q :=
  ![(proof g pk vote out).zero.a,(proof g pk vote out).zero.b,
    (proof g pk vote out).one.a,(proof g pk vote out).one.b]
def scalars (g pk : PrimeGroup p q) (vote : Bool) (out : Draws (q:=q)) : Fin 4 → ZMod q :=
  ![(proof g pk vote out).zero.challenge,(proof g pk vote out).zero.response,
    (proof g pk vote out).one.challenge,(proof g pk vote out).one.response]

theorem scalar_values (g pk : PrimeGroup p q) (vote : Bool) (out : Draws (q:=q)) :
    scalars g pk vote out = ![out.2.2.1,out.2.2.2.1,out.2.1-out.2.2.1,out.2.2.2.2] := rfl

/-- Coordinates remain digits, ready for the existing executed natural-prefix writer. -/
theorem source_groups (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (i : Fin 4) :
    (PrimeProgramCaller.sourceResult slack g pk vote s live out).stk (groupPort i) =
      (primeGroupCoordinate (groups g pk vote out i)).val.bits := by
  fin_cases i <;> rfl

/-- Branch scalars already have the exact canonical original scalar record. -/
theorem source_scalars (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (i : Fin 4) :
    (PrimeProgramCaller.sourceResult slack g pk vote s live out).stk (scalarPort i) =
      scalarEncode (scalars g pk vote out i) := by
  fin_cases i <;> rfl

/-- All fifteen arithmetic work words are genuinely empty in the actual source. -/
theorem source_work (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (j : Fin 15) :
    (PrimeProgramCaller.sourceResult slack g pk vote s live out).stk ⟨23+j.val,by omega⟩ = [] := by
  fin_cases j <;> rfl

/-- Exact seven nested pair records; the full challenge c is represented by e+d. -/
theorem encoding (g pk : PrimeGroup p q) (vote : Bool) (out : Draws (q:=q)) :
    (ballotProofBitCodec p q).encode (proof g pk vote out) =
      bitFieldsEncode [
        bitFieldsEncode [bitFieldsEncode [primeGroupEncode (groups g pk vote out 0),
          primeGroupEncode (groups g pk vote out 1)],
          bitFieldsEncode [scalarEncode (scalars g pk vote out 0),scalarEncode (scalars g pk vote out 1)]],
        bitFieldsEncode [bitFieldsEncode [primeGroupEncode (groups g pk vote out 2),
          primeGroupEncode (groups g pk vote out 3)],
          bitFieldsEncode [scalarEncode (scalars g pk vote out 2),scalarEncode (scalars g pk vote out 3)]]] := rfl

/-- The serializer's scalar operands are the actual preserved resident words. -/
theorem encoding_resident (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let cfg := PrimeProgramCaller.sourceResult slack g pk vote s live out
    (ballotProofBitCodec p q).encode (proof g pk vote out) =
      bitFieldsEncode [
        bitFieldsEncode [bitFieldsEncode [primeGroupEncode (groups g pk vote out 0),
          primeGroupEncode (groups g pk vote out 1)], bitFieldsEncode [cfg.stk 11,cfg.stk 12]],
        bitFieldsEncode [bitFieldsEncode [primeGroupEncode (groups g pk vote out 2),
          primeGroupEncode (groups g pk vote out 3)], bitFieldsEncode [cfg.stk 1,cfg.stk 7]]] := rfl

theorem group_value_lt (g pk : PrimeGroup p q) (vote : Bool) (out : Draws (q:=q)) (i : Fin 4) :
    (primeGroupCoordinate (groups g pk vote out i)).val < p := ZMod.val_lt _
theorem group_word_length (g pk : PrimeGroup p q) (vote : Bool) (out : Draws (q:=q)) (i : Fin 4) :
    (primeGroupEncode (groups g pk vote out i)).length ≤ groupRecordBitBound p :=
  primeGroupEncode_length_le _
theorem scalar_word_length (g pk : PrimeGroup p q) (vote : Bool) (out : Draws (q:=q)) (i : Fin 4) :
    (scalarEncode (scalars g pk vote out i)).length ≤ groupRecordBitBound q := scalarEncode_length_le _
theorem proof_length (g pk : PrimeGroup p q) (vote : Bool) (out : Draws (q:=q)) :
    ((ballotProofBitCodec p q).encode (proof g pk vote out)).length ≤ proofRecordBitBound p q :=
  ballotProofBits_length_le _

/-- Exact bit-width bound on the four resident coordinate operands. -/
theorem source_group_width (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (i : Fin 4) :
    ((PrimeProgramCaller.sourceResult slack g pk vote s live out).stk (groupPort i)).length ≤ (p-1).size := by
  rw [source_groups]
  simpa only [Nat.size_eq_bits_len] using
    Nat.size_le_size (Nat.le_sub_one_of_lt (group_value_lt g pk vote out i))
theorem source_scalar_length (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (i : Fin 4) :
    ((PrimeProgramCaller.sourceResult slack g pk vote s live out).stk (scalarPort i)).length ≤ groupRecordBitBound q := by
  rw [source_scalars]
  exact scalar_word_length g pk vote out i

/-- Both inner group-pair payloads use the existing ciphertext-record bound. -/
theorem group_pair_length (g pk : PrimeGroup p q) (vote : Bool) (out : Draws (q:=q)) (i j : Fin 4) :
    (bitFieldsEncode [primeGroupEncode (groups g pk vote out i),primeGroupEncode (groups g pk vote out j)]).length ≤
      ciphertextRecordBitBound p :=
  BitRecordCodec.pair_length_le (primeGroupBitCodec p q) (primeGroupBitCodec p q) _ _ _ _
    (group_word_length g pk vote out i) (group_word_length g pk vote out j)
/-- Both scalar-pair payloads retain zero values and the original q-bound. -/
theorem scalar_pair_length (g pk : PrimeGroup p q) (vote : Bool) (out : Draws (q:=q)) (i j : Fin 4) :
    (bitFieldsEncode [scalarEncode (scalars g pk vote out i),scalarEncode (scalars g pk vote out j)]).length ≤
      bitPairSize (groupRecordBitBound q) (groupRecordBitBound q) :=
  BitRecordCodec.pair_length_le (primeScalarBitCodec q) (primeScalarBitCodec q) _ _ _ _
    (scalar_word_length g pk vote out i) (scalar_word_length g pk vote out j)
/-- The last pair writer receives two original branch records of bounded size. -/
theorem branch_length (g pk : PrimeGroup p q) (vote : Bool) (out : Draws (q:=q)) (one : Bool) :
    ((ballotBranchBitCodec p q).encode
      (if one then (proof g pk vote out).one else (proof g pk vote out).zero)).length ≤ branchRecordBitBound p q := by
  let b := if one then (proof g pk vote out).one else (proof g pk vote out).zero
  exact BitRecordCodec.pair_length_le (ballotCiphertextBitCodec p q)
    ((primeScalarBitCodec q).pair (primeScalarBitCodec q)) (b.a,b.b) (b.challenge,b.response) _ _
    (BitRecordCodec.pair_length_le (primeGroupBitCodec p q) (primeGroupBitCodec p q) _ _ _ _
      (primeGroupEncode_length_le _) (primeGroupEncode_length_le _))
    (BitRecordCodec.pair_length_le (primeScalarBitCodec q) (primeScalarBitCodec q) _ _ _ _
      (scalarEncode_length_le _) (scalarEncode_length_le _))

#print axioms source_group_width
#print axioms source_scalar_length
#print axioms group_pair_length
#print axioms scalar_pair_length
#print axioms branch_length

#print axioms program_return
#print axioms scalar_values
#print axioms source_groups
#print axioms source_scalars
#print axioms source_work
#print axioms encoding
#print axioms encoding_resident
#print axioms group_value_lt
#print axioms group_word_length
#print axioms scalar_word_length
#print axioms proof_length
end ExplainableCrypto.Helios.Computational.PrimeProgramProofSource
