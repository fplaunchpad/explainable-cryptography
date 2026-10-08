import ExplainableCrypto.Helios.Symbolic.ExpandedPairMinimumTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedSingleMixedTransport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- All expanded local roots except successful decryption/checking are now
supplied by checked theorems. The remaining two cases use the existing generic
DecryptCheckTransport interface with simultaneous smaller-minimum hypotheses. -/
theorem accepted_expanded_joint_local_of_decrypt_check (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (h : Frame.DecryptCheckTransport (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)) :
    Frame.JointLocalMinimumTransport (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) := by
  classical
  intro r hpublic hc hforward hreverse
  have hn := accepted_expanded_results_numeric ns hf left right rs hp haccept swap
  by_cases hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r
  · exact .of_minimal hm
  cases r with
  | name a | var a | const a => exact .of_minimal (.of_nodeCount_one hpublic rfl)
  | unary f a =>
    cases f with
    | pk => exact .of_minimal (expanded_minimum_pk_of_child ns swap left right rs hp hn a hc)
    | fst => exact expanded_minimum_child_projection_shared ns hf swap swap' left right rs hp hn .fst (Or.inl rfl) a hc
    | snd => exact expanded_minimum_child_projection_shared ns hf swap swap' left right rs hp hn .snd (Or.inr rfl) a hc
  | binary f a b =>
    cases f with
    | pair => exact accepted_expanded_minimum_children_pair_shared ns hf swap swap' left right rs hp haccept a b hc.1 hc.2
    | partialDecrypt => exact .of_minimal (expanded_minimum_partial_of_children ns swap left right rs hp hn a b hc.1 hc.2)
    | compose => exact .of_minimal (expanded_minimum_compose_of_children ns swap left right rs hn ns.restricted a b hc.1 hc.2)
    | add => exact accepted_expanded_minimum_children_add_shared ns hf swap swap' left right rs hp haccept a b hc.1 hc.2
    | mul => exact accepted_expanded_minimum_children_mul_shared_of_two_way_minima ns hf swap swap' left right rs hp haccept a b hc.1 hc.2 hforward hreverse
    | dec =>
      by_cases hv : ∃ out, DecryptionMatch ((expandedFrame ns swap left right rs).eval a) ((expandedFrame ns swap left right rs).eval b) out
      · exact h _ hpublic hc hm hv hforward hreverse
      · exact .of_minimal (expanded_minimum_stuck_decryption_of_children ns swap left right rs hn ns.restricted a b hc.1 hc.2
          (fun out he => hv ⟨out,he⟩))
  | ternary f a b c =>
    cases f with
    | penc => exact .of_minimal (expanded_minimum_penc_of_children ns swap left right rs hp hn a b c hc.1 hc.2.1 hc.2.2)
    | checkspk =>
      by_cases hv : ProofCheckMatch ((expandedFrame ns swap left right rs).eval a)
          ((expandedFrame ns swap left right rs).eval b) ((expandedFrame ns swap left right rs).eval c)
      · exact h _ hpublic hc hm hv hforward hreverse
      · exact .of_minimal (expanded_minimum_stuck_check_of_children ns swap left right rs hn ns.restricted a b c hc.1 hc.2.1 hc.2.2 hv)
  | spk a b c d => exact .of_minimal (expanded_minimum_spk_of_children ns swap left right rs hp hn a b c d hc.1 hc.2.1 hc.2.2.1 hc.2.2.2)

/-- Generic simultaneous strong induction discharges all global shared-minimum
premises once the two successful-root transports are supplied. -/
theorem accepted_expanded_common_minima_of_decrypt_check_both (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (hforward : Frame.DecryptCheckTransport (expandedFrame ns false left right rs) (expandedFrame ns true left right rs))
    (hreverse : Frame.DecryptCheckTransport (expandedFrame ns true left right rs) (expandedFrame ns false left right rs)) :
    Frame.CommonMinima (expandedFrame ns false left right rs) (expandedFrame ns true left right rs) ∧
      Frame.CommonMinima (expandedFrame ns true left right rs) (expandedFrame ns false left right rs) :=
  Frame.common_minima_of_joint_local
    (accepted_expanded_joint_local_of_decrypt_check ns hf false true left right rs hp haccept hforward)
    (accepted_expanded_joint_local_of_decrypt_check ns hf true false left right rs hp haccept hreverse)

/-- Only successful decryption/checking transport in both directions remains
as a local premise for the full expanded-frame static-equivalence target. -/
theorem accepted_expanded_staticEq_of_decrypt_check_transport (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (hforward : Frame.DecryptCheckTransport (expandedFrame ns false left right rs) (expandedFrame ns true left right rs))
    (hreverse : Frame.DecryptCheckTransport (expandedFrame ns true left right rs) (expandedFrame ns false left right rs)) :
    Frame.StaticEq (expandedFrame ns false left right rs) (expandedFrame ns true left right rs) :=
  (accepted_expanded_staticEq_iff_common_minima ns hf left right rs hp haccept).mpr
    (accepted_expanded_common_minima_of_decrypt_check_both ns hf left right rs hp haccept hforward hreverse)

/-- The same remaining successful-root premises suffice for the actual final
public transcript, including published partials and results. -/
theorem accepted_final_staticEq_of_decrypt_check_transport (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (hforward : Frame.DecryptCheckTransport (expandedFrame ns false left right rs) (expandedFrame ns true left right rs))
    (hreverse : Frame.DecryptCheckTransport (expandedFrame ns true left right rs) (expandedFrame ns false left right rs)) :
    Frame.StaticEq (finalFrame ns false left right rs) (finalFrame ns true left right rs) :=
  (accepted_final_staticEq_iff_expanded_common_minima ns hf left right rs hp haccept).mpr
    (accepted_expanded_common_minima_of_decrypt_check_both ns hf left right rs hp haccept hforward hreverse)

/-- Public result reconstruction also gives the aggregate-partial target from
the same two remaining successful-root transports. -/
theorem accepted_partial_staticEq_of_decrypt_check_transport (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (hforward : Frame.DecryptCheckTransport (expandedFrame ns false left right rs) (expandedFrame ns true left right rs))
    (hreverse : Frame.DecryptCheckTransport (expandedFrame ns true left right rs) (expandedFrame ns false left right rs)) :
    Frame.StaticEq (partialFrame ns false left right rs) (partialFrame ns true left right rs) :=
  (accepted_partial_staticEq_iff_expanded_common_minima ns hf left right rs hp haccept).mpr
    (accepted_expanded_common_minima_of_decrypt_check_both ns hf left right rs hp haccept hforward hreverse)

end ExplainableCrypto.Helios.Symbolic.Historical.General
