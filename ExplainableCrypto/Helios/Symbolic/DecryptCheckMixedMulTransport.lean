import ExplainableCrypto.Helios.Symbolic.JointMinimumTransport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat} {restricted : Finset Nat}

/-- Only products with both public constructed and honest contributions remain
in this case. The assembly records the exact recipe and actual key coherence. -/
def MixedCiphertextProduct (n : Nat) (φ : Frame restricted 3) (r : Recipe 3) : Prop :=
  ∃ t : CiphertextAssembly n, t.recipe = r ∧ t.Coherent φ ∧
    ∃ nonce payload honest, t.group = .mixed nonce payload honest

def DecryptCheckMixedMulCase (n : Nat) (φ : Frame restricted 3) : Recipe 3 → Prop
  | .binary .dec a b => ∃ m, DecryptionMatch (φ.eval a) (φ.eval b) m
  | .ternary .checkspk a b c => ProofCheckMatch (φ.eval a) (φ.eval b) (φ.eval c)
  | .binary .mul a b => MixedCiphertextProduct n φ (.binary .mul a b)
  | _ => False

/-- The remaining cases may use both strict smaller-minimum induction
hypotheses. Their instances for the actual frames are still proof obligations. -/
def DecryptCheckMixedMulTransport (n : Nat) (φ ψ : Frame restricted 3) : Prop :=
  ∀ r, r.Public restricted → Frame.MinimumChildren φ r →
    ¬ MinimalRecipe restricted φ.value r → DecryptCheckMixedMulCase n φ r →
    Frame.SharedMinimaBelow φ ψ r.nodeCount → Frame.SharedMinimaBelow ψ φ r.nodeCount →
    Frame.SharedMinimum φ ψ r

/-- Honest-only products are minimum; constructed-only products strictly
compress under the derived bounded observations. Mixed products and successful
destructors are the only remaining cases in the simultaneous local step. -/
theorem joint_local_of_decrypt_check_mixed_mul (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty)
    (h : DecryptCheckMixedMulTransport n (frame ns swap left right) (frame ns swap' left right)) :
    Frame.JointLocalMinimumTransport (frame ns swap left right) (frame ns swap' left right) := by
  classical
  intro r hp hc hsmall hreverse
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
      · obtain ⟨t,ht,hpT,hcoh,hgroup⟩ := nonminimum_ciphertext_product_public_group
          ns hf swap left right a b hc.1 hc.2 hm hv
        rcases hgroup with ⟨nr,p,hg⟩ | ⟨nr,p,c,hg⟩
        · cases t with
          | constructed k nr' p' => cases ht
          | honest i => simp only [CiphertextAssembly.recipe,Term.project] at ht; cases ht
          | mul u v =>
            have hsmallT : Frame.SharedMinimaBelow (frame ns swap left right)
                (frame ns swap' left right) (u.mul v).recipe.nodeCount := ht.symm ▸ hsmall
            have hreverseT : Frame.SharedMinimaBelow (frame ns swap' left right)
                (frame ns swap left right) (u.mul v).recipe.nodeCount := ht.symm ▸ hreverse
            exact ht ▸ constructed_mul_shared_of_two_way_minima ns hf swap swap' left right
              u v hpT hg hcoh hsmallT hreverseT
        · exact h _ hp hc hm ⟨t,ht,hcoh,nr,p,c,hg⟩ hsmall hreverse
      · exact minimum_children_non_ciphertext_mul_shared ns swap left right _ a b hc.1 hc.2 hv hsmall
    | dec =>
      by_cases hv : ∃ m, DecryptionMatch ((frame ns swap left right).eval a) ((frame ns swap left right).eval b) m
      · exact h _ hp hc hm hv hsmall hreverse
      · exact .of_minimal (minimum_stuck_decryption_of_children ns swap left right a b hc.1 hc.2
          (fun m he => hv ⟨m,he⟩))
  | ternary f a b c =>
    cases f with
    | penc => exact .of_minimal (minimum_penc_of_children ns swap left right a b c hc.1 hc.2.1 hc.2.2)
    | checkspk =>
      by_cases hv : ProofCheckMatch ((frame ns swap left right).eval a)
          ((frame ns swap left right).eval b) ((frame ns swap left right).eval c)
      · exact h _ hp hc hm hv hsmall hreverse
      · exact .of_minimal (minimum_stuck_check_of_children ns swap left right a b c hc.1 hc.2.1 hc.2.2 hv)
  | spk a b c d => exact .of_minimal (minimum_spk_of_children ns swap left right a b c d hc.1 hc.2.1 hc.2.2.1 hc.2.2.2)

/-- Simultaneous unbounded recipe induction discharges all constructed and
honest products. The remaining mixed-product/successful-destructor premises in
both directions are explicit and must still be proved for the actual frames. -/
theorem staticEq_of_decrypt_check_mixed_mul_transport (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty)
    (hforward : DecryptCheckMixedMulTransport n (frame ns false left right) (frame ns true left right))
    (hreverse : DecryptCheckMixedMulTransport n (frame ns true left right) (frame ns false left right)) :
    Frame.StaticEq (frame ns false left right) (frame ns true left right) :=
  (staticEq_iff_common_minima ns hf left right).mpr
    (Frame.common_minima_of_joint_local
      (joint_local_of_decrypt_check_mixed_mul ns hf false true left right hforward)
      (joint_local_of_decrypt_check_mixed_mul ns hf true false left right hreverse))

end ExplainableCrypto.Helios.Symbolic.Historical.General
