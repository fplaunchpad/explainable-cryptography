import ExplainableCrypto.Helios.Symbolic.InductiveMinimumTransport

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {n : Nat}

/-- Only successful destructors and products evaluating to one ciphertext
remain after non-ciphertext product reassembly by strict recipe induction. -/
def DecryptCheckCipherMulCase (φ : Frame restricted n) : Recipe n → Prop
  | .binary .dec a b => ∃ m, DecryptionMatch (φ.eval a) (φ.eval b) m
  | .ternary .checkspk a b c => ProofCheckMatch (φ.eval a) (φ.eval b) (φ.eval c)
  | .binary .mul a b => (φ.eval (.binary .mul a b)).CiphertextValue
  | _ => False

def DecryptCheckCipherMulTransport (φ ψ : Frame restricted n) : Prop :=
  ∀ r, r.Public restricted → MinimumChildren φ r →
    ¬ MinimalRecipe restricted φ.value r → DecryptCheckCipherMulCase φ r → SharedMinimum φ ψ r

end ExplainableCrypto.Helios.Symbolic.Frame

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Previously checked local cases and the strict smaller-piece theorem
assemble the inductive local step. Whole-ciphertext products remain a premise. -/
theorem inductive_local_of_decrypt_check_cipher_mul (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty)
    (h : Frame.DecryptCheckCipherMulTransport (frame ns swap left right) (frame ns swap' left right)) :
    Frame.InductiveLocalMinimumTransport (frame ns swap left right) (frame ns swap' left right) := by
  classical
  intro r hp hc hsmall
  by_cases hm : MinimalRecipe ns.restricted (frame ns swap left right).value r
  · exact .of_minimal hm
  cases r with
  | name a => exact .of_minimal (.of_nodeCount_one hp rfl)
  | var a => exact .of_minimal (.of_nodeCount_one hp rfl)
  | const a => exact .of_minimal (.of_nodeCount_one hp rfl)
  | unary f a =>
    cases f with
    | pk => exact .of_minimal (minimum_pk_of_child ns swap left right a hc)
    | fst => exact minimum_child_projection_shared ns hf swap swap' left right .fst (Or.inl rfl) a hc
    | snd => exact minimum_child_projection_shared ns hf swap swap' left right .snd (Or.inr rfl) a hc
  | binary f a b =>
    cases f with
    | pair => exact minimum_children_pair_shared ns hf swap swap' left right a b hc.1 hc.2
    | compose => exact .of_minimal (minimum_compose_of_children ns swap left right ns.restricted a b hc.1 hc.2)
    | add => exact minimum_children_add_shared ns swap left right a b hc.1 hc.2 _
    | partialDecrypt => exact .of_minimal (minimum_partial_of_children ns swap left right a b hc.1 hc.2)
    | mul =>
      by_cases hv : ((frame ns swap left right).eval (.binary .mul a b)).CiphertextValue
      · exact h _ hp hc hm hv
      · exact minimum_children_non_ciphertext_mul_shared ns swap left right _ a b hc.1 hc.2 hv hsmall
    | dec =>
      by_cases hv : ∃ m, DecryptionMatch ((frame ns swap left right).eval a) ((frame ns swap left right).eval b) m
      · exact h _ hp hc hm hv
      · exact .of_minimal (minimum_stuck_decryption_of_children ns swap left right a b hc.1 hc.2
          (fun m he => hv ⟨m,he⟩))
  | ternary f a b c =>
    cases f with
    | penc => exact .of_minimal (minimum_penc_of_children ns swap left right a b c hc.1 hc.2.1 hc.2.2)
    | checkspk =>
      by_cases hv : ProofCheckMatch ((frame ns swap left right).eval a)
          ((frame ns swap left right).eval b) ((frame ns swap left right).eval c)
      · exact h _ hp hc hm hv
      · exact .of_minimal (minimum_stuck_check_of_children ns swap left right a b c hc.1 hc.2.1 hc.2.2 hv)
  | spk a b c d => exact .of_minimal (minimum_spk_of_children ns swap left right a b c d hc.1 hc.2.1 hc.2.2.1 hc.2.2.2)

/-- Initial-frame static equivalence now needs only successful decryption,
successful checking and whole-ciphertext product shared minima in both swaps.
Non-ciphertext products are discharged by well-founded size induction. -/
theorem staticEq_of_decrypt_check_cipher_mul_transport (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty)
    (hforward : Frame.DecryptCheckCipherMulTransport (frame ns false left right) (frame ns true left right))
    (hreverse : Frame.DecryptCheckCipherMulTransport (frame ns true left right) (frame ns false left right)) :
    Frame.StaticEq (frame ns false left right) (frame ns true left right) :=
  (staticEq_iff_common_minima ns hf left right).mpr
    ⟨Frame.common_minima_of_inductive_local
      (inductive_local_of_decrypt_check_cipher_mul ns hf false true left right hforward),
     Frame.common_minima_of_inductive_local
      (inductive_local_of_decrypt_check_cipher_mul ns hf true false left right hreverse)⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
