import ExplainableCrypto.Helios.Symbolic.CiphertextKeyTransfer
import ExplainableCrypto.Helios.Symbolic.ExpandedPublicKeyTransport
import ExplainableCrypto.Helios.Symbolic.ValueShapeTransfer

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- An actual honest selector retains the one-node election-key handle.
The numeric source premise excludes ciphertexts hidden in result slots. -/
theorem expanded_projection_ciphertext_key_transfer (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (v : Fin (ExpandedHandles n))
    (r : Recipe (ExpandedHandles n)) (hc : ProjectionChain v r) {key nonce message : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.ternary .penc key nonce message)) :
    ∃ k : Recipe (ExpandedHandles n), k.Public ns.restricted ∧ k.nodeCount < r.nodeCount ∧
      EqE ((expandedFrame ns swap left right rs).eval k) key ∧ ∃ nonce' message',
        EqE ((expandedFrame ns swap' left right rs).eval r)
          (.ternary .penc ((expandedFrame ns swap' left right rs).eval k) nonce' message') := by
  obtain ⟨i,j,_,rfl,hval⟩ := expanded_projection_ciphertext_origin ns swap left right rs hn v hc he
  refine ⟨.var (expandedOld 0),trivial,?_,?_,.name (ns.nonce i j),(choice swap' left right i).value j,?_⟩
  · have hpos := ((Term.var (expandedOld (n := n) i.succ) : Recipe (ExpandedHandles n)).drop j.val).nodeCount_pos
    simp only [Term.project,Term.nodeCount]
    omega
  · rw [expanded_election_handle_value]
    exact ((EqE.penc_iff _ _ _ _ _ _).mp hval).1
  · rw [expanded_election_handle_value,Frame.eval,Term.subst_project,Term.subst,
      expanded_frame_old,frame_voter_handle]
    exact ballot_project_ciphertext ns i (choice swap' left right i).value j

/-- Value transport for the existing constructor/selector/product grammar;
no minimum premise or new grouping representation is used. -/
theorem expanded_ciphertext_syntax_key_transfer (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs)
    (r : Recipe (ExpandedHandles n)) (hs : CiphertextRecipeSyntax r) (hp : r.Public ns.restricted)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow
      (expandedFrame ns swap' left right rs) r.nodeCount) {key nonce message : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.ternary .penc key nonce message)) :
    ∃ k : Recipe (ExpandedHandles n), k.Public ns.restricted ∧ k.nodeCount < r.nodeCount ∧
      EqE ((expandedFrame ns swap left right rs).eval k) key ∧ ∃ nonce' message',
        EqE ((expandedFrame ns swap' left right rs).eval r)
          (.ternary .penc ((expandedFrame ns swap' left right rs).eval k) nonce' message') :=
  Frame.ciphertext_syntax_key_transfer _ _
    (fun v r hc _ _ _ he => expanded_projection_ciphertext_key_transfer ns swap swap' left right rs hn v r hc he)
    r hs hp hobs he

/-- Source minimum size supplies the ciphertext grammar. Smaller observations
are the sole remaining transport premise after source origins are discharged. -/
theorem expanded_minimum_ciphertext_key_transfer (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs)
    (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow
      (expandedFrame ns swap' left right rs) r.nodeCount) {key nonce message : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.ternary .penc key nonce message)) :
    ∃ k : Recipe (ExpandedHandles n), k.Public ns.restricted ∧ k.nodeCount < r.nodeCount ∧
      EqE ((expandedFrame ns swap left right rs).eval k) key ∧ ∃ nonce' message',
        EqE ((expandedFrame ns swap' left right rs).eval r)
          (.ternary .penc ((expandedFrame ns swap' left right rs).eval k) nonce' message') :=
  expanded_ciphertext_syntax_key_transfer ns swap swap' left right rs hn r
    (expanded_minimum_ciphertext_syntax ns swap left right rs hn ns.restricted r hm he) hm.isPublic hobs he

/-- Accepted public submissions discharge the numeric origin premise. -/
theorem accepted_expanded_minimum_ciphertext_key_transfer (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow
      (expandedFrame ns swap' left right rs) r.nodeCount) {key nonce message : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.ternary .penc key nonce message)) :
    ∃ k : Recipe (ExpandedHandles n), k.Public ns.restricted ∧ k.nodeCount < r.nodeCount ∧
      EqE ((expandedFrame ns swap left right rs).eval k) key ∧ ∃ nonce' message',
        EqE ((expandedFrame ns swap' left right rs).eval r)
          (.ternary .penc ((expandedFrame ns swap' left right rs).eval k) nonce' message') :=
  expanded_minimum_ciphertext_key_transfer ns swap swap' left right rs
    (accepted_expanded_results_numeric ns hf left right rs hp ha swap) r hm hobs he

theorem accepted_expanded_minimum_ciphertext_value_transfer (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow
      (expandedFrame ns swap' left right rs) r.nodeCount)
    (he : ((expandedFrame ns swap left right rs).eval r).CiphertextValue) :
    ((expandedFrame ns swap' left right rs).eval r).CiphertextValue := by
  obtain ⟨key,nonce,message,he⟩ := he
  obtain ⟨k,_,_,_,nonce',message',hv⟩ := accepted_expanded_minimum_ciphertext_key_transfer
    ns hf swap swap' left right rs hp ha r hm hobs he
  exact ⟨_,nonce',message',hv⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
