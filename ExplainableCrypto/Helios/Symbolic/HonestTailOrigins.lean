import ExplainableCrypto.Helios.Symbolic.HonestFieldTransport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- A minimum equivalent of a nonempty honest tail is exactly that indexed
tail. Constructed pairs pay a strictly greater cost for the first field. -/
theorem minimum_honest_tail_origin (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns swap left right).value r)
    (i : Fin 2) (k : Nat) (hk : k < fieldCount n)
    (he : EqE ((frame ns swap left right).eval r)
      ((frame ns swap left right).eval ((Term.var i.succ).drop k))) :
    r = (Term.var i.succ).drop k := by
  obtain ⟨x,y,hv⟩ := ballot_tail_pair_value ns swap left right i k hk
  rcases minimum_pair_observation_form ns swap left right ns.restricted r hm (he.trans hv) with
    ⟨u,v,rfl⟩ | ⟨j,l,hl,rfl⟩
  · have hfield : EqE ((frame ns swap left right).eval u)
        ((frame ns swap left right).eval ((Term.var i.succ).project k)) :=
      (RootStep.fst _ _).sound.symm.trans (.unary .fst he)
    have hbound := honest_field_public_size_bound ns hf swap left right u hm.isPublic.1 i k hk hfield
    have hsize := hm.least ((Term.var i.succ).drop k)
      ((ProjectionChain.drop i.succ k).isPublic _) he
    have := v.nodeCount_pos
    simp only [Term.nodeCount, Term.drop_nodeCount] at hsize
    omega
  · have hi := (ballot_tail_equality_iff ns hf swap left right j i l k hl hk).mp he
    rcases hi with ⟨rfl,rfl⟩
    rfl

/-- A minimum match to any honest tail transfers, including the empty suffix
whose minimum representative is literal bottom. -/
theorem minimum_honest_tail_match_transfer (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns swap left right).value r)
    (i : Fin 2) (k : Nat) (hk : k ≤ fieldCount n)
    (he : EqE ((frame ns swap left right).eval r)
      ((frame ns swap left right).eval ((Term.var i.succ).drop k))) :
    EqE ((frame ns swap' left right).eval r)
      ((frame ns swap' left right).eval ((Term.var i.succ).drop k)) := by
  by_cases hlt : k < fieldCount n
  · rw [minimum_honest_tail_origin ns hf swap left right r hm i k hlt he]
    exact .refl _
  · have value (s : Bool) :
        EqE ((frame ns s left right).eval ((Term.var i.succ).drop k)) (.const .bottom) := by
      have hlen : (ballotFields ns i (choice s left right i).value).length ≤ k := by
        rw [ballot_fields_length]; omega
      simpa only [List.drop_eq_nil_of_le hlen, Term.tuple] using
        ballot_tail_recipe_value ns s left right i k hk
    have hr := minimum_constant_form ns swap left right ns.restricted r hm .bottom (he.trans (value swap))
    rw [hr]
    exact (value swap').symm

end ExplainableCrypto.Helios.Symbolic.Historical.General
