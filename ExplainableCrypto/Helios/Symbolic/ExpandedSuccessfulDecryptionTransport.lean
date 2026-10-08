import ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulCheckTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedRootAssembly
import ExplainableCrypto.Helios.Symbolic.SuccessfulDecryptionTransport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Successful checking discharges the second residual root; the remaining
interface is exactly successful decryption, with the same strict induction bounds. -/
theorem accepted_expanded_decrypt_check_transport_of_successful_decryption (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (h : Frame.SuccessfulDecryptionTransport (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)) :
    Frame.DecryptCheckTransport (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) := by
  intro r hpub hc hm hv hforward hreverse
  cases r with
  | name _ | var _ | const _ | unary _ _ | spk _ _ _ _ => cases hv
  | binary f a b =>
    cases f with
    | pair | compose | add | partialDecrypt | mul => cases hv
    | dec => exact h _ hpub hc hm hv hforward hreverse
  | ternary f a b c =>
    cases f with
    | penc => cases hv
    | checkspk =>
      exact accepted_expanded_minimum_children_check_shared_of_two_way_minima ns hf swap swap' left right rs hp haccept
        a b c hc.1 hc.2.1 hc.2.2 hforward hreverse

/-- The expanded-frame target now requires only the two successful-decryption
transports. No separate checking, observation or global minimum premise remains. -/
theorem accepted_expanded_staticEq_of_successful_decryption_transport (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (hforward : Frame.SuccessfulDecryptionTransport (expandedFrame ns false left right rs) (expandedFrame ns true left right rs))
    (hreverse : Frame.SuccessfulDecryptionTransport (expandedFrame ns true left right rs) (expandedFrame ns false left right rs)) :
    Frame.StaticEq (expandedFrame ns false left right rs) (expandedFrame ns true left right rs) :=
  accepted_expanded_staticEq_of_decrypt_check_transport ns hf left right rs hp haccept
    (accepted_expanded_decrypt_check_transport_of_successful_decryption ns hf false true left right rs hp haccept hforward)
    (accepted_expanded_decrypt_check_transport_of_successful_decryption ns hf true false left right rs hp haccept hreverse)

/-- The aggregate-partial target now requires only the two successful-decryption
transports. No separate checking, observation or global minimum premise remains. -/
theorem accepted_partial_staticEq_of_successful_decryption_transport (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (hforward : Frame.SuccessfulDecryptionTransport (expandedFrame ns false left right rs) (expandedFrame ns true left right rs))
    (hreverse : Frame.SuccessfulDecryptionTransport (expandedFrame ns true left right rs) (expandedFrame ns false left right rs)) :
    Frame.StaticEq (partialFrame ns false left right rs) (partialFrame ns true left right rs) :=
  accepted_partial_staticEq_of_decrypt_check_transport ns hf left right rs hp haccept
    (accepted_expanded_decrypt_check_transport_of_successful_decryption ns hf false true left right rs hp haccept hforward)
    (accepted_expanded_decrypt_check_transport_of_successful_decryption ns hf true false left right rs hp haccept hreverse)

/-- The actual final-frame target now requires only the two successful-decryption
transports. No separate checking, observation or global minimum premise remains. -/
theorem accepted_final_staticEq_of_successful_decryption_transport (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (hforward : Frame.SuccessfulDecryptionTransport (expandedFrame ns false left right rs) (expandedFrame ns true left right rs))
    (hreverse : Frame.SuccessfulDecryptionTransport (expandedFrame ns true left right rs) (expandedFrame ns false left right rs)) :
    Frame.StaticEq (finalFrame ns false left right rs) (finalFrame ns true left right rs) :=
  accepted_final_staticEq_of_decrypt_check_transport ns hf left right rs hp haccept
    (accepted_expanded_decrypt_check_transport_of_successful_decryption ns hf false true left right rs hp haccept hforward)
    (accepted_expanded_decrypt_check_transport_of_successful_decryption ns hf true false left right rs hp haccept hreverse)

end ExplainableCrypto.Helios.Symbolic.Historical.General
