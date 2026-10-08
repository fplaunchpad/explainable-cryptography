import ExplainableCrypto.Helios.Symbolic.SingleMixedMinimumClosure

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {n : Nat}

/-- Multiplication is discharged. Only successful decryption and proof
checking remain in the local induction interface. -/
def DecryptCheckCase (φ : Frame restricted n) : Recipe n → Prop
  | .binary .dec a b => ∃ m, DecryptionMatch (φ.eval a) (φ.eval b) m
  | .ternary .checkspk a b c => ProofCheckMatch (φ.eval a) (φ.eval b) (φ.eval c)
  | _ => False

def DecryptCheckTransport (φ ψ : Frame restricted n) : Prop :=
  ∀ r, r.Public restricted → MinimumChildren φ r →
    ¬ MinimalRecipe restricted φ.value r → DecryptCheckCase φ r →
    SharedMinimaBelow φ ψ r.nodeCount → SharedMinimaBelow ψ φ r.nodeCount →
    SharedMinimum φ ψ r

end ExplainableCrypto.Helios.Symbolic.Frame

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- The one-constructor mixed branch is now closed. Its actual nonce/payload
minima follow from minimum immediate children, and simultaneous smaller minima
supply the observation bound needed for key agreement in the destination. -/
theorem single_mixed_transport_of_decrypt_check (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty)
    (h : Frame.DecryptCheckTransport (frame ns swap left right) (frame ns swap' left right)) :
    DecryptCheckSingleMixedTransport n (frame ns swap left right) (frame ns swap' left right) := by
  intro r hp hc hm hv hforward hreverse
  cases r with
  | name _ | var _ | const _ | unary _ _ | spk _ _ _ _ => cases hv
  | ternary f a b c =>
    cases f with
    | penc => cases hv
    | checkspk => exact h _ hp hc hm hv hforward hreverse
  | binary f a b =>
    cases f with
    | pair | compose | add | partialDecrypt => cases hv
    | dec => exact h _ hp hc hm hv hforward hreverse
    | mul =>
      obtain ⟨t,ht,hcoh,hcount,nr,p,c,hg⟩ := hv
      have hleaf : ∀ x ∈ t.recipe.mulLeaves, MinimalRecipe ns.restricted (frame ns swap left right).value x := by
        intro x hx
        rw [ht] at hx
        rcases Multiset.mem_add.mp hx with ha | hb
        · exact hc.1.mul_leaf ha
        · exact hc.2.mul_leaf hb
      have hobs := observationsBelow_of_two_way_minima ns hf swap swap' left right _ hforward hreverse
      exact ht ▸ single_mixed_shared_of_smaller_observations ns hf swap swap' left right t
        (ht.symm ▸ hp) hleaf hcount hg hcoh (ht.symm ▸ hobs)

/-- All multiplication classes are discharged in the unbounded recipe
induction. Successful decryption/checking in both directions remain explicit. -/
theorem staticEq_of_decrypt_check_transport (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty)
    (hforward : Frame.DecryptCheckTransport (frame ns false left right) (frame ns true left right))
    (hreverse : Frame.DecryptCheckTransport (frame ns true left right) (frame ns false left right)) :
    Frame.StaticEq (frame ns false left right) (frame ns true left right) :=
  staticEq_of_decrypt_check_single_mixed_transport ns hf left right
    (single_mixed_transport_of_decrypt_check ns hf false true left right hforward)
    (single_mixed_transport_of_decrypt_check ns hf true false left right hreverse)

end ExplainableCrypto.Helios.Symbolic.Historical.General
