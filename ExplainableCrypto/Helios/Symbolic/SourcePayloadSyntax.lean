import ExplainableCrypto.Helios.Symbolic.SourceInputBinding

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type} {n : Nat}

/-- Source bulletin-board product, seeded by the two honest ciphertext fields.
The nonempty product introduces no term-level identity. -/
def boardTally (first second : Term V) (others : List (Term V)) (j : Fin (n+1)) : Term V :=
  others.foldl (fun acc b => .binary .mul acc (b.project j.val))
    (.binary .mul (first.project j.val) (second.project j.val))

def tallyMessage (first second : Term V) (others : List (Term V)) : Term V :=
  candidateTuple (n := n) (boardTally first second others)

/-- The source trustee's input continuation: its fresh tally variable is None.
The secret is lifted past the binder; all candidate projections are explicit. -/
def trusteeBody (secret : Term V) : Term (Option V) :=
  candidateTuple (n := n) (fun j => .binary .partialDecrypt
    (secret.subst (fun v => .var (some v))) ((Term.var none).project j.val))

/-- The source bulletin-board result continuation. The freshly received tuple
is None; the previously sent tallies are lifted past this input binder. -/
def resultBody (tallies : Term V) : Term (Option V) :=
  candidateTuple (n := n) (fun j => .binary .dec ((Term.var none).project j.val)
    ((tallies.subst (fun v => .var (some v))).project j.val))

/-- Literal source expressions after both private communications. These keep
all tuple projections and input substitutions, before using E to simplify. -/
def trusteeMessage (secret tallies : Term V) : Term V :=
  bindInput (trusteeBody (n := n) secret) tallies

def resultMessage (tallies partials : Term V) : Term V :=
  bindInput (resultBody (n := n) tallies) partials

def sourceTallies (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) : Ground :=
  tallyMessage (n := n) (ballot ns 0 (choice swap left right 0).value)
    (ballot ns 1 (choice swap left right 1).value) (rs.map (frame ns swap left right).eval)

def sourcePartials (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) : Ground :=
  trusteeMessage (n := n) (.name ns.secretKey) (sourceTallies ns swap left right rs)

def sourceResults (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) : Ground :=
  resultMessage (n := n) (sourceTallies ns swap left right rs) (sourcePartials ns swap left right rs)

def sourcePartialFrame (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) : Frame ns.restricted 4 :=
  (frame ns swap left right).extend (sourcePartials ns swap left right rs)

def sourceFinalFrame (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) : Frame ns.restricted 5 :=
  (sourcePartialFrame ns swap left right rs).extend (sourceResults ns swap left right rs)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
