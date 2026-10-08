import ExplainableCrypto.Helios.Symbolic.SharedTally

namespace ExplainableCrypto.Helios.Symbolic
variable {restricted : Finset Nat} {handles : Nat} {V : Type}

/-- Append one observed value while retaining every previous handle. -/
def Frame.extend (φ : Frame restricted handles) (value : Ground) : Frame restricted (handles+1) :=
  ⟨Fin.lastCases value φ.value⟩

def Recipe.lift (r : Recipe handles) : Recipe (handles+1) :=
  r.subst (fun i => .var i.castSucc)

/-- A complete ordered tuple over all candidates, using the existing bottom
terminated tuple encoding. -/
def candidateTuple {n : Nat} (values : Fin (n+1) → Term V) : Term V :=
  Term.tuple ((List.finRange (n+1)).map values)

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Handles 0–2 retain the initial frame; handle 3 publishes the complete
candidate tuple of partial decryptions of the actual tally ciphertexts. -/
def partialFrame (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) : Frame ns.restricted 4 :=
  (frame ns swap left right).extend (candidateTuple (tallyPartial ns swap left right rs))

/-- Handle 4 publishes every candidate's actual result expression. -/
def finalFrame (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) : Frame ns.restricted 5 :=
  (partialFrame ns swap left right rs).extend (candidateTuple (tallyResult ns swap left right rs))

/-- Public computation of the result tuple from the already-published partial
tuple and the ciphertext aggregates, retaining the complete E6 binding. -/
def resultRecipe (rs : List (Recipe 3)) : Recipe 4 :=
  candidateTuple (n := n) (fun j => .binary .dec ((Term.var 3).project j.val) (tallyRecipe rs j).lift)

end ExplainableCrypto.Helios.Symbolic.Historical.General
