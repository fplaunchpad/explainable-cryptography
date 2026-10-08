import ExplainableCrypto.Helios.Symbolic.ExpandedTrusteeBinding

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Retained initial handles and numeric result slots, as a derived proof
presentation. The actual protocol still publishes its full defined transcript. -/
def ResultHandles (n : Nat) : Nat := 3+(n+1)
def resultOld (i : Fin 3) : Fin (ResultHandles n) := Fin.castAdd (n+1) i
def resultSlot (j : Fin (n+1)) : Fin (ResultHandles n) := Fin.natAdd 3 j
def resultEmbedding : Fin (ResultHandles n) → Fin (ExpandedHandles n) :=
  Fin.addCases expandedOld expandedResult

def resultFrame (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) : Frame ns.restricted (ResultHandles n) :=
  (expandedFrame ns swap left right rs).derive (fun i => .var (resultEmbedding i))

/-- Each known numeric result is replaced by a nonempty public numeral. -/
def resultNumeralRecipes (numbers : Fin (n+1) → Nat) : Fin (ResultHandles n) → Recipe 3 :=
  Fin.addCases Term.var (fun j => addNumeral (numbers j))

theorem result_embedding_old (i : Fin 3) : resultEmbedding (resultOld (n := n) i) = expandedOld i := by
  simp [resultEmbedding,resultOld]
theorem result_embedding_slot (j : Fin (n+1)) : resultEmbedding (resultSlot j) = expandedResult j := by
  simp [resultEmbedding,resultSlot]
theorem result_numeral_old (numbers : Fin (n+1) → Nat) (i : Fin 3) :
    resultNumeralRecipes numbers (resultOld i) = .var i := by
  simp [resultNumeralRecipes,resultOld]
theorem result_numeral_slot (numbers : Fin (n+1) → Nat) (j : Fin (n+1)) :
    resultNumeralRecipes numbers (resultSlot j) = addNumeral (numbers j) := by
  simp [resultNumeralRecipes,resultSlot]

theorem result_numeral_public (numbers : Fin (n+1) → Nat) (restricted : Finset Nat)
    (v : Fin (ResultHandles n)) : (resultNumeralRecipes numbers v).Public restricted := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) v
  · simp only [resultNumeralRecipes,Fin.addCases_left,Term.Public]
  · simp only [resultNumeralRecipes,Fin.addCases_right]
    have h (k : Nat) : (addNumeral k : Recipe 3).Public restricted := by
      induction k <;> simp_all [addNumeral,Term.Public]
    exact h _

theorem result_recipe_public (r : Recipe (ResultHandles n)) (restricted : Finset Nat)
    (hr : r.Public restricted) : (r.subst (fun i => .var (resultEmbedding i))).Public restricted :=
  Term.Public.subst r _ hr (fun _ => trivial)

theorem result_recipe_erasure_public (numbers : Fin (n+1) → Nat) (r : Recipe (ResultHandles n))
    (restricted : Finset Nat) (hr : r.Public restricted) : (r.subst (resultNumeralRecipes numbers)).Public restricted :=
  Term.Public.subst r _ hr (result_numeral_public numbers restricted)

end ExplainableCrypto.Helios.Symbolic.Historical.General
