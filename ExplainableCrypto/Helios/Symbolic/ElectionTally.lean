import ExplainableCrypto.Helios.Symbolic.SuccessfulDecryptionClosure
import ExplainableCrypto.Helios.Symbolic.GeneralStaticTransfer

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {handles : Nat}

/-- All submissions pass in order; each successful submission extends the
board used to check later submissions. Rejection is not silently skipped. -/
def AcceptsSequence (φ : Frame restricted handles) (n : Nat) (key : Recipe handles)
    (board : List (Recipe handles)) : List (Recipe handles) → Prop
  | [] => True
  | r :: rs => Accepted n (φ.eval key) (board.map φ.eval) (φ.eval r) ∧
      φ.AcceptsSequence n key (board ++ [r]) rs

end ExplainableCrypto.Helios.Symbolic.Frame

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

def honestBoardRecipes : List (Recipe 3) := [.var 1,.var 2]

/-- Aggregate one candidate across the two honest ballots and all accepted
submissions. The seed contains two ciphertexts; there is no empty product. -/
def tallyRecipe (submissions : List (Recipe 3)) (j : Fin (n+1)) : Recipe 3 :=
  submissions.foldl (fun acc r => .binary .mul acc (r.project j.val))
    (.binary .mul ((Term.var 1).project j.val) ((Term.var 2).project j.val))

def tallyCiphertext (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (submissions : List (Recipe 3)) (j : Fin (n+1)) : Ground :=
  (frame ns swap left right).eval (tallyRecipe submissions j)

def tallyPartial (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (submissions : List (Recipe 3)) (j : Fin (n+1)) : Ground :=
  .binary .partialDecrypt (.name ns.secretKey) (tallyCiphertext ns swap left right submissions j)

/-- The actual published result expression uses E6 on the matching partial
decryption and whole tally ciphertext. -/
def tallyResult (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (submissions : List (Recipe 3)) (j : Fin (n+1)) : Ground :=
  .binary .dec (tallyPartial ns swap left right submissions j)
    (tallyCiphertext ns swap left right submissions j)

end ExplainableCrypto.Helios.Symbolic.Historical.General
