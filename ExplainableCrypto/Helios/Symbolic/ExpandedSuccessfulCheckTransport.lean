import ExplainableCrypto.Helios.Symbolic.ExpandedHonestFieldTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedMinimumLifting
import ExplainableCrypto.Helios.Symbolic.SuccessfulCheckTransport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- A minimum match to an honest combination gives equality of the recipes
before either frame is substituted. No oversized aggregate observation is used. -/
theorem expanded_minimum_honest_combination_recipe_eqE (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (r : Recipe (ExpandedHandles n)) (hr : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (a : Combination (HonestIndex n))
    (he : EqE ((expandedFrame ns swap left right rs).eval r)
      ((expandedFrame ns swap left right rs).eval (combinationRecipeWith expandedOld a))) :
    EqE r (combinationRecipeWith expandedOld a) := by
  obtain ⟨b,rfl,hb⟩ := expanded_minimum_honest_combination_origin ns hf swap left right rs hp hn r hr a he
  have hraw : BaseEq (combinationRecipe b) (combinationRecipe a) :=
    Combination.evaluate_baseEq_of_indices .mul trivial _ hb
  exact hraw.sound.subst _

/-- Retained honest component checks are valid independently of publication. -/
theorem expanded_honest_component_check_recipe_valid (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (i : Fin 2) (j : Fin (n+1)) :
    EqE ((expandedFrame ns swap left right rs).eval (.ternary .checkspk (.var (expandedOld 0))
      (combinationRecipeWith expandedOld (.leaf (i,j)))
      ((Term.var (expandedOld i.succ)).project (n+1+j.val)))) (.const .ok) := by
  have h := honest_component_check_recipe_valid ns swap left right i j
  simpa only [combinationRecipeWith,expanded_old_recipe_value,Frame.eval,Term.subst,
    Term.subst_project,Term.subst_subst,expanded_frame_old] using h

/-- The aggregate binds the complete nonempty ciphertext combination. -/
theorem expanded_honest_aggregate_check_recipe_valid (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (i : Fin 2) :
    EqE ((expandedFrame ns swap left right rs).eval (.ternary .checkspk (.var (expandedOld 0))
      (combinationRecipeWith expandedOld (voterCombination (n := n) i))
      ((Term.var (expandedOld i.succ)).project (2*(n+1))))) (.const .ok) := by
  have h := honest_aggregate_check_recipe_valid ns swap left right i
  simpa only [combinationRecipeWith,expanded_old_recipe_value,Frame.eval,Term.subst,
    Term.subst_project,Term.subst_subst,expanded_frame_old] using h

/-- Honest proof success transports its whole ciphertext binding through the
minimum combination origin. Only the key test needs smaller observations. -/
theorem expanded_honest_check_success_transfer (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hpub : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (a b c : Recipe (ExpandedHandles n)) (ha : a.Public ns.restricted)
    (hb : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b)
    (t : Combination (HonestIndex n))
    (hp : ∃ r m, EqE ((expandedFrame ns swap left right rs).eval c)
      (.spk (publicKey ns) r m ((expandedFrame ns swap left right rs).eval (combinationRecipeWith expandedOld t))))
    (hvalid : EqE (.ternary .checkspk (publicKey ns)
      ((expandedFrame ns swap' left right rs).eval (combinationRecipeWith expandedOld t))
      ((expandedFrame ns swap' left right rs).eval c)) (.const .ok))
    (hobs : Frame.ObservationsBelow (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)
      (Term.ternary .checkspk a b c).nodeCount)
    (he : EqE ((expandedFrame ns swap left right rs).eval (.ternary .checkspk a b c)) (.const .ok)) :
    EqE ((expandedFrame ns swap' left right rs).eval (.ternary .checkspk a b c)) (.const .ok) := by
  obtain ⟨r,m,hp⟩ := hp
  obtain ⟨nr,bit,_,_,hproof⟩ := (EqE.check_ok_iff_components _ _ _).mp he
  have hs := (EqE.spk_iff _ _ _ _ _ _ _ _).mp (hp.symm.trans hproof)
  have hraw := expanded_minimum_honest_combination_recipe_eqE ns hf swap left right rs hpub hn b hb t hs.2.2.2.symm
  have hk : EqE ((expandedFrame ns swap' left right rs).eval a) (publicKey ns) := by
    have hkey := (hobs a (.var (expandedOld 0)) ha trivial (by
      have hcpos := c.nodeCount_pos
      simp only [Term.nodeCount]
      omega)).mp (by rw [expanded_election_handle_value]; exact hs.1.symm)
    rw [expanded_election_handle_value] at hkey
    exact hkey
  exact (EqE.ternary .checkspk hk (hraw.subst _) (.refl _)).trans hvalid

/-- Minimum proof origins exhaust constructed and borrowed proofs even with
published handles. Constructed checks reuse the generic four-test argument. -/
theorem expanded_minimum_check_success_transfer (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (a b c : Recipe (ExpandedHandles n)) (ha : a.Public ns.restricted)
    (hb : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b)
    (hc : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value c)
    (hobs : Frame.ObservationsBelow (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)
      (Term.ternary .checkspk a b c).nodeCount)
    (he : EqE ((expandedFrame ns swap left right rs).eval (.ternary .checkspk a b c)) (.const .ok)) :
    EqE ((expandedFrame ns swap' left right rs).eval (.ternary .checkspk a b c)) (.const .ok) := by
  obtain ⟨nr,bit,_,_,hproof⟩ := (EqE.check_ok_iff_components _ _ _).mp he
  have form := expanded_minimum_proof_form ns swap left right rs hn ns.restricted c hc hproof
  rcases form with ⟨k,r,m,d,rfl⟩ | ⟨i,j,rfl⟩ | ⟨i,rfl⟩
  · exact constructed_check_success_transfer _ _ a b k r m d ha hb.isPublic hc.isPublic hobs he
  · apply expanded_honest_check_success_transfer ns hf swap swap' left right rs hp hn a b _ ha hb (.leaf (i,j)) ?_
      (expanded_honest_component_check_recipe_valid ns swap' left right rs i j) hobs he
    exact ⟨.name (ns.nonce i j),(choice swap left right i).value j,
      (expanded_component_proof_value ns swap left right rs i j).trans
        (.spk (.refl _) (.refl _) (.refl _) (expanded_combination_value ns swap left right rs (.leaf (i,j))).symm)⟩
  · apply expanded_honest_check_success_transfer ns hf swap swap' left right rs hp hn a b _ ha hb (voterCombination i) ?_
      (expanded_honest_aggregate_check_recipe_valid ns swap' left right rs i) hobs he
    have hv : EqE ((expandedFrame ns swap left right rs).eval (combinationRecipeWith expandedOld (voterCombination (n := n) i)))
        (foldCandidates .mul (ciphertext ns i (choice swap left right i).value)) := by
      rw [combinationRecipeWith,expanded_old_recipe_value]
      exact voterCombination_value ns swap left right i
    exact ⟨foldCandidates .compose (fun j => .name (ns.nonce i j)),
      foldCandidates .add (choice swap left right i).value,
      (expanded_aggregate_proof_value ns swap left right rs i).trans
        (.spk (.refl _) (.refl _) (.refl _) hv.symm)⟩

/-- Both successful and stuck checking close under exactly the two smaller
minimum hypotheses supplied by simultaneous recipe induction. -/
theorem accepted_expanded_minimum_children_check_shared_of_two_way_minima (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (a b c : Recipe (ExpandedHandles n))
    (ha : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a)
    (hb : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b)
    (hc : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value c)
    (hforward : Frame.SharedMinimaBelow (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)
      (Term.ternary .checkspk a b c).nodeCount)
    (hreverse : Frame.SharedMinimaBelow (expandedFrame ns swap' left right rs) (expandedFrame ns swap left right rs)
      (Term.ternary .checkspk a b c).nodeCount) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) (.ternary .checkspk a b c) := by
  classical
  have hn := accepted_expanded_results_numeric ns hf left right rs hp haccept swap
  by_cases hs : ProofCheckMatch ((expandedFrame ns swap left right rs).eval a)
      ((expandedFrame ns swap left right rs).eval b) ((expandedFrame ns swap left right rs).eval c)
  · have he := hs.reduces.sound
    exact ⟨.const .ok,.of_nodeCount_one trivial rfl,he,
      expanded_minimum_check_success_transfer ns hf swap swap' left right rs hp hn a b c ha.isPublic hb hc
        (accepted_expanded_observationsBelow_of_two_way_minima ns hf swap swap' left right rs hp haccept _ hforward hreverse) he⟩
  · exact .of_minimal (expanded_minimum_stuck_check_of_children ns swap left right rs hn ns.restricted a b c ha hb hc hs)

end ExplainableCrypto.Helios.Symbolic.Historical.General
