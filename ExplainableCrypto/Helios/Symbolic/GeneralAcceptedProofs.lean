import ExplainableCrypto.Helios.Symbolic.BallotValues
import ExplainableCrypto.Helios.Symbolic.GeneralMinimumProofs

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Weeding removes the honest component-selector branch of minimum proof forms.
The board must actually contain both initial honest ballots. -/
theorem minimum_accepted_component_proof_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat)
    (board : List Ground) (b : Ground)
    (ha : Accepted n (publicKey ns) board b)
    (hboard : ∀ i : Fin 2, ballot ns i ((choice swap left right i).value) ∈ board)
    (j : Fin (n + 1)) (recipe : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value recipe)
    (he : EqE ((frame ns swap left right).eval recipe) (b.project (n + 1 + j.val))) :
    (∃ a b c d, recipe = .spk a b c d) ∨
      ∃ i : Fin 2, recipe = (Term.var i.succ).project (2 * (n + 1)) := by
  obtain ⟨r, bit, _, _, hp⟩ := (EqE.check_ok_iff_components _ _ _).mp (ha.1.2 j)
  rcases minimum_proof_form ns swap left right restricted recipe hm (he.trans hp) with
    hc | ⟨i, k, hr⟩ | hg
  · exact Or.inl hc
  · subst recipe
    have he' : EqE ((ballot ns i ((choice swap left right i).value)).project (n + 1 + k.val))
        (b.project (n + 1 + j.val)) := by
      simpa only [Frame.eval, Term.subst_project, Term.subst, frame_voter_handle] using he
    exact False.elim (accepted_component_proof_not_reused ha (hboard i)
      (honest_proofs_valid ns i (choice swap left right i).value (choice swap left right i).valid) k j he')
  · exact Or.inr hg

/-- A minimum accepted component proof either supplies a public nonce recipe or
is an honest aggregate selector. The latter case still needs exclusion. -/
theorem accepted_component_nonce_or_aggregate (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat)
    (board : List Ground) (b : Ground)
    (ha : Accepted n (publicKey ns) board b)
    (hboard : ∀ i : Fin 2, ballot ns i ((choice swap left right i).value) ∈ board)
    (j : Fin (n + 1)) (recipe : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value recipe)
    (he : EqE ((frame ns swap left right).eval recipe) (b.project (n + 1 + j.val)))
    (r m : Ground) (hp : EqE (b.project (n + 1 + j.val))
      (.spk (publicKey ns) r m (b.project j.val))) :
    (∃ s : Recipe 3, s.Public restricted ∧ EqE ((frame ns swap left right).eval s) r) ∨
      ∃ i : Fin 2, recipe = (Term.var i.succ).project (2 * (n + 1)) := by
  rcases minimum_accepted_component_proof_form ns swap left right restricted board b
      ha hboard j recipe hm he with ⟨a, s, c, d, hr⟩ | hg
  · subst recipe
    have hnonce := ((EqE.spk_iff _ _ _ _ _ _ _ _).mp (he.trans hp)).2.1
    exact Or.inl ⟨s, hm.isPublic.2.1, hnonce⟩
  · exact Or.inr hg

end ExplainableCrypto.Helios.Symbolic.Historical.General
