import ExplainableCrypto.Helios.Computational.PrimeSimAllCommitCallerSource
import ExplainableCrypto.Helios.Computational.BallotCacheBitSize

/-! Source operands for the original simulator hash key. These presentation
laws derive digits from the actual reached state; serialization execution is
provided separately and is not a premise of these laws. -/
namespace ExplainableCrypto.Helios.Computational.PrimeSimKeySource

/-- Exact key used when programming the first simulated ballot proof. -/
def key {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    BallotForkPoint (PrimeGroup p q) :=
  let stmt := honestProofStatement g pk (vote,out.1.1)
  (stmt,ballotSimCommit stmt out.2.1 (out.2.2.1,out.2.2.2.1,out.2.2.2.2))

/-- Order is fixed by ballotKeyRecord, including both ciphertext coordinates. -/
def ports : List (Fin 43) := [16,15,17,0,3,38,40,42]

theorem source_digits {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    ports.map (PrimeSimAllCommitCaller.sourceResult slack g pk vote saved out).stk =
      (ballotKeyRecord (key g pk vote out)).map
        (fun x => (primeGroupCoordinate x).val.bits) := rfl

/-- The existing cache key codec uses a count and a length frame around every
canonical coordinate prefix; digit concatenation alone is not that codec. -/
theorem encoding {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    (ballotKeyBitCodec p q).encode (key g pk vote out) =
      uniformNatEncode 8 ++ bitFramesEncode
        ((ballotKeyRecord (key g pk vote out)).map
          (fun x => uniformNatEncode (primeGroupCoordinate x).val)) := rfl

/-- All eight coordinate widths follow from the typed source, including
identity commitments, without an exact-order assumption. -/
theorem source_width {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q))
    (word : List Bool)
    (hw : word ∈ ports.map (PrimeSimAllCommitCaller.sourceResult slack g pk vote saved out).stk) :
    word.length ≤ (p-1).size := by
  rw [source_digits] at hw
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hw
  have h := (primeGroupCoordinate x).val_lt
  simpa only [←Nat.size_eq_bits_len] using Nat.size_le_size (show (primeGroupCoordinate x).val ≤ p-1 by omega)

/-- Existing arithmetic work is empty in the reached result, so the concrete
key serializer can reuse these five ports while preserving every live word. -/
theorem source_work {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q))
    (j : Fin 5) :
    (PrimeSimAllCommitCaller.sourceResult slack g pk vote saved out).stk
      ⟨23+j.val,by omega⟩ = [] := by
  fin_cases j <;> rfl

#print axioms source_work

#print axioms source_digits
#print axioms encoding
#print axioms source_width
end ExplainableCrypto.Helios.Computational.PrimeSimKeySource
