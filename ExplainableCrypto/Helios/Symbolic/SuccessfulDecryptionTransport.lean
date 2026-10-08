import ExplainableCrypto.Helios.Symbolic.SuccessfulCheckTransport

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {n : Nat}

/-- Only successful decryption remains in the local induction interface. -/
def SuccessfulDecryptionCase (φ : Frame restricted n) : Recipe n → Prop
  | .binary .dec a b => ∃ m, DecryptionMatch (φ.eval a) (φ.eval b) m
  | _ => False

def SuccessfulDecryptionTransport (φ ψ : Frame restricted n) : Prop :=
  ∀ r, r.Public restricted → MinimumChildren φ r →
    ¬ MinimalRecipe restricted φ.value r → SuccessfulDecryptionCase φ r →
    SharedMinimaBelow φ ψ r.nodeCount → SharedMinimaBelow ψ φ r.nodeCount →
    SharedMinimum φ ψ r

end ExplainableCrypto.Helios.Symbolic.Frame

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Full checking transport discharges the check branch of the preceding
interface using exactly the two smaller-minimum induction hypotheses. -/
theorem decrypt_check_transport_of_successful_decryption (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty)
    (h : Frame.SuccessfulDecryptionTransport (frame ns swap left right) (frame ns swap' left right)) :
    Frame.DecryptCheckTransport (frame ns swap left right) (frame ns swap' left right) := by
  intro r hp hc hm hv hforward hreverse
  cases r with
  | name _ | var _ | const _ | unary _ _ | spk _ _ _ _ => cases hv
  | binary f a b =>
    cases f with
    | pair | compose | add | partialDecrypt | mul => cases hv
    | dec => exact h _ hp hc hm hv hforward hreverse
  | ternary f a b c =>
    cases f with
    | penc => cases hv
    | checkspk =>
      exact minimum_children_check_shared_of_two_way_minima ns hf swap swap' left right
        a b c hc.1 hc.2.1 hc.2.2 hforward hreverse

/-- Conditional sufficient criterion for initial static equivalence. The
successful-decryption instances in both directions still require proof. -/
theorem staticEq_of_successful_decryption_transport (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty)
    (hforward : Frame.SuccessfulDecryptionTransport (frame ns false left right) (frame ns true left right))
    (hreverse : Frame.SuccessfulDecryptionTransport (frame ns true left right) (frame ns false left right)) :
    Frame.StaticEq (frame ns false left right) (frame ns true left right) :=
  staticEq_of_decrypt_check_transport ns hf left right
    (decrypt_check_transport_of_successful_decryption ns hf false true left right hforward)
    (decrypt_check_transport_of_successful_decryption ns hf true false left right hreverse)

end ExplainableCrypto.Helios.Symbolic.Historical.General
