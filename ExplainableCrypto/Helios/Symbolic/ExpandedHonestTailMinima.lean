import ExplainableCrypto.Helios.Symbolic.ExpandedPairTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedHonestFieldTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedAtomicTransport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- A minimum match to a nonempty honest tail is exactly that indexed tail.
An explicit pair would pay too much for its first field even with new handles. -/
theorem expanded_minimum_honest_tail_origin (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (i : Fin 2) (k : Nat) (hk : k<fieldCount n)
    (he : EqE ((expandedFrame ns swap left right rs).eval r)
      ((expandedFrame ns swap left right rs).eval ((Term.var (expandedOld i.succ)).drop k))) :
    r=(Term.var (expandedOld i.succ)).drop k := by
  obtain ⟨x,y,hv⟩ := expanded_ballot_tail_pair_value ns swap left right rs i k hk
  rcases expanded_minimum_pair_observation_form ns swap left right rs hn ns.restricted r hm (he.trans hv) with
    ⟨u,v,rfl⟩ | ⟨j,l,hl,rfl⟩
  · have hfield : EqE ((expandedFrame ns swap left right rs).eval u)
        ((expandedFrame ns swap left right rs).eval ((Term.var (expandedOld i.succ)).project k)) :=
      (RootStep.fst _ _).sound.symm.trans (.unary .fst he)
    have hbound := expanded_honest_field_public_size_bound ns hf swap left right rs hp hn u hm.isPublic.1 i k hk hfield
    have hsize := hm.least ((Term.var (expandedOld i.succ)).drop k)
      ((ProjectionChain.drop (expandedOld i.succ) k).isPublic _) he
    have := v.nodeCount_pos
    simp only [Term.nodeCount,Term.drop_nodeCount] at hsize
    omega
  · have hi := (expanded_ballot_tail_equality_iff ns hf swap left right rs j i l k hl hk).mp he
    rcases hi with ⟨rfl,rfl⟩
    rfl

/-- Every nonempty retained honest tail remains globally minimum after
publication, against all expanded public recipes, at its exact k+1 cost. -/
theorem expanded_minimum_ballot_tail (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (i : Fin 2) (k : Nat) (hk : k<fieldCount n) :
    MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value ((Term.var (expandedOld i.succ)).drop k) := by
  have hpub := (ProjectionChain.drop (expandedOld (n := n) i.succ) k).isPublic ns.restricted
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame ns swap left right rs).value) _ hpub
  have h := expanded_minimum_honest_tail_origin ns hf swap left right rs hp hn m hm i k hk he.symm
  simpa only [h] using hm

/-- The first empty tail is literal bottom in every assignment. -/
theorem expanded_empty_ballot_tail_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (i : Fin 2) :
    EqE ((expandedFrame ns swap left right rs).eval ((Term.var (expandedOld i.succ)).drop (fieldCount n))) (.const .bottom) := by
  have ht := expanded_ballot_tail_value ns swap left right rs i (fieldCount n) (by rfl)
  have hl : (ballotFields ns i (choice swap left right i).value).length=fieldCount n := ballot_fields_length _ _ _
  simpa only [← hl,List.drop_length,Term.tuple] using ht

/-- Nonempty tails use themselves; the empty tail uses the one-node bottom
recipe. Both replacements are valid without smaller induction hypotheses. -/
theorem expanded_ballot_tail_shared_minimum (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (i : Fin 2) (k : Nat) (hk : k≤fieldCount n) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)
      ((Term.var (expandedOld i.succ)).drop k) := by
  by_cases hlt : k<fieldCount n
  · exact .of_minimal (expanded_minimum_ballot_tail ns hf swap left right rs hp hn i k hlt)
  · have he : k=fieldCount n := by omega
    subst k
    exact ⟨.const .bottom,.of_nodeCount_one trivial rfl,
      expanded_empty_ballot_tail_value ns swap left right rs i,expanded_empty_ballot_tail_value ns swap' left right rs i⟩

/-- Minimum matches to tails transfer. The empty suffix reuses accepted atomic
value transfer, retaining the possibility of a published constant alias. -/
theorem accepted_expanded_minimum_honest_tail_match_transfer (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (i : Fin 2) (k : Nat) (hk : k≤fieldCount n)
    (he : EqE ((expandedFrame ns swap left right rs).eval r)
      ((expandedFrame ns swap left right rs).eval ((Term.var (expandedOld i.succ)).drop k))) :
    EqE ((expandedFrame ns swap' left right rs).eval r)
      ((expandedFrame ns swap' left right rs).eval ((Term.var (expandedOld i.succ)).drop k)) := by
  by_cases hlt : k<fieldCount n
  · rw [expanded_minimum_honest_tail_origin ns hf swap left right rs hp
      (accepted_expanded_results_numeric ns hf left right rs hp haccept swap) r hm i k hlt he]
    exact .refl _
  · have hkEq : k=fieldCount n := by omega
    subst k
    exact (accepted_expanded_minimum_atomic_value_transfer ns hf swap swap' left right rs hp haccept r hm
      (.const .bottom) rfl (he.trans (expanded_empty_ballot_tail_value ns swap left right rs i))).trans
      (expanded_empty_ballot_tail_value ns swap' left right rs i).symm

end ExplainableCrypto.Helios.Symbolic.Historical.General
