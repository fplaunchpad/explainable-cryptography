import ExplainableCrypto.Helios.Symbolic.MixedCompression

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat} {restricted : Finset Nat}

/-- A mixed assembly with exactly one public constructed occurrence. The
honest combination can still contain arbitrarily many indexed occurrences. -/
def SingleMixedProduct (n : Nat) (φ : Frame restricted 3) (r : Recipe 3) : Prop :=
  ∃ t : CiphertextAssembly n, t.recipe=r ∧ t.Coherent φ ∧ t.constructedCount=1 ∧
    ∃ nonce payload honest, t.group=.mixed nonce payload honest

def DecryptCheckSingleMixedCase (n : Nat) (φ : Frame restricted 3) : Recipe 3 → Prop
  | .binary .dec a b => ∃ m, DecryptionMatch (φ.eval a) (φ.eval b) m
  | .ternary .checkspk a b c => ProofCheckMatch (φ.eval a) (φ.eval b) (φ.eval c)
  | .binary .mul a b => SingleMixedProduct n φ (.binary .mul a b)
  | _ => False

def DecryptCheckSingleMixedTransport (n : Nat) (φ ψ : Frame restricted 3) : Prop :=
  ∀ r, r.Public restricted → Frame.MinimumChildren φ r →
    ¬ MinimalRecipe restricted φ.value r → DecryptCheckSingleMixedCase n φ r →
    Frame.SharedMinimaBelow φ ψ r.nodeCount → Frame.SharedMinimaBelow ψ φ r.nodeCount →
    Frame.SharedMinimum φ ψ r

/-- Strict mixed compression discharges every case with two or more public
constructors. The remaining interface retains one-constructor mixed products. -/
theorem mixed_transport_of_single_mixed_transport (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty)
    (h : DecryptCheckSingleMixedTransport n (frame ns swap left right) (frame ns swap' left right)) :
    DecryptCheckMixedMulTransport n (frame ns swap left right) (frame ns swap' left right) := by
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
      obtain ⟨t,ht,hcoh,nr,p,c,hg⟩ := hv
      by_cases hcount : 2 ≤ t.constructedCount
      · have hpT : t.recipe.Public ns.restricted := ht.symm ▸ hp
        have hfT : Frame.SharedMinimaBelow (frame ns swap left right)
            (frame ns swap' left right) t.recipe.nodeCount := ht.symm ▸ hforward
        have hrT : Frame.SharedMinimaBelow (frame ns swap' left right)
            (frame ns swap left right) t.recipe.nodeCount := ht.symm ▸ hreverse
        exact ht ▸ mixed_compression_shared_of_two_way_minima ns hf swap swap' left right t
          hpT hg hcoh hcount hfT hrT
      · have hpos := t.mixed_constructedCount_pos hg
        exact h _ hp hc hm ⟨t,ht,hcoh,by omega,nr,p,c,hg⟩ hforward hreverse

/-- The unbounded secrecy route now retains only one-constructor mixed
products and successful destructors. Both remaining instances are explicit. -/
theorem staticEq_of_decrypt_check_single_mixed_transport (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty)
    (hforward : DecryptCheckSingleMixedTransport n (frame ns false left right) (frame ns true left right))
    (hreverse : DecryptCheckSingleMixedTransport n (frame ns true left right) (frame ns false left right)) :
    Frame.StaticEq (frame ns false left right) (frame ns true left right) :=
  staticEq_of_decrypt_check_mixed_mul_transport ns hf left right
    (mixed_transport_of_single_mixed_transport ns hf false true left right hforward)
    (mixed_transport_of_single_mixed_transport ns hf true false left right hreverse)

end ExplainableCrypto.Helios.Symbolic.Historical.General
