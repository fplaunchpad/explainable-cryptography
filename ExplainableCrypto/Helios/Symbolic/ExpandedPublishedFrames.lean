import ExplainableCrypto.Helios.Symbolic.PublishedProtection

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- The first three handles, followed by all partials, then all results. This
is a publicly interderivable proof presentation of the tuple frame. -/
abbrev ExpandedHandles (n : Nat) := 3 + ((n+1) + (n+1))

def expandedOld (i : Fin 3) : Fin (ExpandedHandles n) := i.castAdd ((n+1)+(n+1))
def expandedPartial (j : Fin (n+1)) : Fin (ExpandedHandles n) := (j.castAdd (n+1)).natAdd 3
def expandedResult (j : Fin (n+1)) : Fin (ExpandedHandles n) := (j.natAdd (n+1)).natAdd 3

def expandedFrame (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) : Frame ns.restricted (ExpandedHandles n) :=
  ⟨Fin.addCases (frame ns swap left right).value
    (Fin.addCases (tallyPartial ns swap left right rs) (tallyResult ns swap left right rs))⟩

/-- Obtain individual slots solely by public projection from the final frame. -/
def expandedRecipes : Fin (ExpandedHandles n) → Recipe 5 :=
  Fin.addCases (fun i => .var i.castSucc.castSucc)
    (Fin.addCases (fun j : Fin (n+1) => (Term.var 3).project j.val)
      (fun j : Fin (n+1) => (Term.var 4).project j.val))

/-- Reconstruct the original two tuples from all their individual slots. -/
def tupleRecipes : Fin 5 → Recipe (ExpandedHandles n) :=
  Fin.lastCases (candidateTuple (fun j : Fin (n+1) => .var (expandedResult j)))
    (Fin.lastCases (candidateTuple (fun j : Fin (n+1) => .var (expandedPartial j)))
      (fun i => .var (expandedOld i)))

end ExplainableCrypto.Helios.Symbolic.Historical.General
