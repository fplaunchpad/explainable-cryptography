import ExplainableCrypto.Helios.Symbolic.ExpandedOldRecipeTools
import ExplainableCrypto.Helios.Symbolic.ExpandedHonestMinima

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Any expanded minimum matching an honest field still uses an old public
recipe. Opaque nonce protection excludes newly constructed proof matches;
honest ciphertext combination origins supply the ciphertext case. -/
theorem expanded_minimum_honest_field_old (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (i : Fin 2) (k : Nat) (hk : k<fieldCount n)
    (he : EqE ((expandedFrame ns swap left right rs).eval r)
      ((expandedFrame ns swap left right rs).eval ((Term.var (expandedOld i.succ)).project k))) :
    ∃ old : Recipe 3, old.Public ns.restricted ∧ r=old.subst (fun i => .var (expandedOld i)) := by
  have hlen : k<(ballotFields ns i (choice swap left right i).value).length := by
    simpa only [ballot_fields_length] using hk
  rcases ballot_field_cases ns i (choice swap left right i).value k hlen with
    ⟨j,rfl,_⟩ | ⟨j,rfl,_⟩ | ⟨rfl,_⟩
  · have hex : EqE ((expandedFrame ns swap left right rs).eval r)
        ((expandedFrame ns swap left right rs).eval (combinationRecipeWith expandedOld (.leaf (i,j)))) := by
      simpa only [combinationRecipeWith,combinationRecipe,Combination.evaluate,Term.subst_project,Term.subst] using he
    obtain ⟨b,hb,_⟩ := expanded_minimum_honest_combination_origin ns hf swap left right rs hp hn r hm (.leaf (i,j)) hex
    exact ⟨combinationRecipe b,combinationRecipe_public _ _,hb⟩
  · have hv := he.trans (expanded_component_proof_value ns swap left right rs i j)
    rcases expanded_minimum_proof_form ns swap left right rs hn ns.restricted r hm hv with ⟨a,b,c,d,rfl⟩ | hborrow
    · exact False.elim (expanded_constructed_proof_not_component ns swap left right rs hp a b c d hm.isPublic.2.1 i j hv)
    · exact expanded_borrowed_proof_old ns.restricted r hborrow
  · have hv := he.trans (expanded_aggregate_proof_value ns swap left right rs i)
    rcases expanded_minimum_proof_form ns swap left right rs hn ns.restricted r hm hv with ⟨a,b,c,d,rfl⟩ | hborrow
    · exact False.elim (expanded_constructed_proof_not_aggregate ns swap left right rs hp a b c d hm.isPublic.2.1 i hv)
    · exact expanded_borrowed_proof_old ns.restricted r hborrow

/-- Minimum matches to honest fields transfer by B7, including the shorter
one-candidate aggregate alias. No smaller-observation premise is needed. -/
theorem expanded_minimum_honest_field_match_transfer (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (i : Fin 2) (k : Nat) (hk : k<fieldCount n)
    (he : EqE ((expandedFrame ns swap left right rs).eval r)
      ((expandedFrame ns swap left right rs).eval ((Term.var (expandedOld i.succ)).project k))) :
    EqE ((expandedFrame ns swap' left right rs).eval r)
      ((expandedFrame ns swap' left right rs).eval ((Term.var (expandedOld i.succ)).project k)) := by
  obtain ⟨old,hpub,rfl⟩ := expanded_minimum_honest_field_old ns hf swap left right rs hp hn r hm i k hk he
  simpa only [Term.subst_project,Term.subst] using
    (expanded_old_equality_swap ns hf swap swap' left right rs old ((Term.var i.succ).project k)
      hpub ((ProjectionChain.project i.succ k).isPublic _)).mp
      (by simpa only [Term.subst_project,Term.subst] using he)

/-- Every public expanded recipe matching honest field k pays at least k+1
nodes. This reuses the initial bound after classifying a global minimum. -/
theorem expanded_honest_field_public_size_bound (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (r : Recipe (ExpandedHandles n)) (hr : r.Public ns.restricted)
    (i : Fin 2) (k : Nat) (hk : k<fieldCount n)
    (he : EqE ((expandedFrame ns swap left right rs).eval r)
      ((expandedFrame ns swap left right rs).eval ((Term.var (expandedOld i.succ)).project k))) : k+1≤r.nodeCount := by
  obtain ⟨m,hm,hem⟩ := exists_minimal_recipe (σ := (expandedFrame ns swap left right rs).value) r hr
  obtain ⟨old,hpub,rfl⟩ := expanded_minimum_honest_field_old ns hf swap left right rs hp hn m hm i k hk (hem.symm.trans he)
  have hsize := hm.least r hr hem.symm
  rw [Term.nodeCount_subst_var] at hsize
  have hvalue : EqE ((frame ns swap left right).eval old) ((frame ns swap left right).eval ((Term.var i.succ).project k)) := by
    have hex := hem.symm.trans he
    change EqE ((expandedFrame ns swap left right rs).eval (old.subst (fun i => .var (expandedOld i)))) _ at hex
    rw [expanded_old_recipe_value] at hex
    simpa only [Frame.eval,Term.subst_project,Term.subst,expanded_frame_old] using hex
  have hb := honest_field_public_size_bound ns hf swap left right old hpub i k hk hvalue
  omega

/-- Every honest field selector has an actual shared expanded minimum. The
selector itself need not be minimum, as the one-candidate aggregate shows. -/
theorem expanded_honest_field_shared_minimum (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (i : Fin 2) (k : Nat) (hk : k<fieldCount n) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)
      ((Term.var (expandedOld i.succ)).project k) := by
  have h := expanded_old_shared_of_minimum_origins ns hf swap swap' left right rs ((Term.var i.succ).project k)
    ((ProjectionChain.project i.succ k).isPublic _) (fun m hm he =>
      expanded_minimum_honest_field_old ns hf swap left right rs hp hn m hm i k hk
        (by simpa only [Term.subst_project,Term.subst] using he))
  simpa only [Term.subst_project,Term.subst] using h

end ExplainableCrypto.Helios.Symbolic.Historical.General
