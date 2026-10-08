import ExplainableCrypto.Helios.Symbolic.ExpandedStuckOrigins
import ExplainableCrypto.Helios.Symbolic.ExpandedDecryptionTransport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- A minimum argument with no source pair value remains unsuitable for either
projection. Accepted elections discharge both numeric premises of reflection. -/
theorem accepted_expanded_minimum_no_pair_swap (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (a : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a)
    (hn : ∀ x y, ¬ EqE ((expandedFrame ns swap left right rs).eval a) (.binary .pair x y))
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs) a.nodeCount) :
    ∀ x y, ¬ EqE ((expandedFrame ns swap' left right rs).eval a) (.binary .pair x y) := by
  intro x y he
  obtain ⟨u,v,hv⟩ := (accepted_expanded_minimum_value_shapes_swap ns hf swap swap' left right rs hp ha a hm hobs).1.mpr ⟨x,y,he⟩
  exact hn u v hv

/-- Arbitrary source-minimum recipes with stuck projection values retain both
selector and argument equality. Full-E origins and destination no-pair facts
are derived, including targets whose arguments themselves reduce. -/
theorem accepted_expanded_minimum_stuck_projection_equality_swap (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value s)
    (f g : Unary) (hf' : f = .fst ∨ f = .snd) (hg : g = .fst ∨ g = .snd)
    {a b : Ground} (hna : ∀ x y, ¬ EqE a (.binary .pair x y)) (hnb : ∀ x y, ¬ EqE b (.binary .pair x y))
    (her : EqE ((expandedFrame ns swap left right rs).eval r) (.unary f a))
    (hes : EqE ((expandedFrame ns swap left right rs).eval s) (.unary g b))
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs)
      (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns swap left right rs).eval r) ((expandedFrame ns swap left right rs).eval s) ↔
      EqE ((expandedFrame ns swap' left right rs).eval r) ((expandedFrame ns swap' left right rs).eval s) := by
  have hn := accepted_expanded_results_numeric ns hf left right rs hp ha swap
  obtain ⟨u,rfl,hu⟩ := expanded_minimum_stuck_projection_form ns swap left right rs hn ns.restricted r hr f hf' hna her
  obtain ⟨v,rfl,hv⟩ := expanded_minimum_stuck_projection_form ns swap left right rs hn ns.restricted s hs g hg hnb hes
  have hu' := accepted_expanded_minimum_no_pair_swap ns hf swap swap' left right rs hp ha u
    (hr.subterm (.unary f .hole)) hu (hobs.mono (by simp only [Term.nodeCount]; omega))
  have hv' := accepted_expanded_minimum_no_pair_swap ns hf swap swap' left right rs hp ha v
    (hs.subterm (.unary g .hole)) hv (hobs.mono (by simp only [Term.nodeCount]; omega))
  have harg := hobs u v hr.isPublic hs.isPublic (by simp only [Term.nodeCount]; omega)
  exact (EqE.projection_iff_of_no_pair f g hf' hg _ _ hu hv).trans
    ((and_congr Iff.rfl harg).trans (EqE.projection_iff_of_no_pair f g hf' hg _ _ hu' hv').symm)

/-- Arbitrary source-minimum recipes with stuck decryption values have exact
ordered syntax. The existing result-handle probes then transfer E5/E6 failure
within the ordinary two-recipe observation budget. -/
theorem accepted_expanded_minimum_stuck_decryption_equality_swap (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value s)
    {a b c d : Ground} (hnr : ∀ out, ¬ DecryptionMatch a b out) (hns : ∀ out, ¬ DecryptionMatch c d out)
    (her : EqE ((expandedFrame ns swap left right rs).eval r) (.binary .dec a b))
    (hes : EqE ((expandedFrame ns swap left right rs).eval s) (.binary .dec c d))
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs)
      (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns swap left right rs).eval r) ((expandedFrame ns swap left right rs).eval s) ↔
      EqE ((expandedFrame ns swap' left right rs).eval r) ((expandedFrame ns swap' left right rs).eval s) := by
  have hn := accepted_expanded_results_numeric ns hf left right rs hp ha swap
  obtain ⟨u,v,rfl,_⟩ := expanded_minimum_stuck_decryption_form ns swap left right rs hn ns.restricted r hr hnr her
  obtain ⟨w,x,rfl,_⟩ := expanded_minimum_stuck_decryption_form ns swap left right rs hn ns.restricted s hs hns hes
  exact accepted_expanded_minimum_decryption_equality_swap ns hf swap swap' left right rs hp ha u v w x hr hs hobs

end ExplainableCrypto.Helios.Symbolic.Historical.General
