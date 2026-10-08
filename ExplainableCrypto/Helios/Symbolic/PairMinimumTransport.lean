import ExplainableCrypto.Helios.Symbolic.HonestTailOrigins

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- A pair of source-minimum children has a shared source-minimum. An explicit
minimum competitor forces minimum size for the original pair; an honest-tail
competitor transfers through exact field and tail matches. -/
theorem minimum_children_pair_shared (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (a b : Recipe 3)
    (ha : MinimalRecipe ns.restricted (frame ns swap left right).value a)
    (hb : MinimalRecipe ns.restricted (frame ns swap left right).value b) :
    Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right) (.binary .pair a b) := by
  have hp : (Term.binary .pair a b).Public ns.restricted := ⟨ha.isPublic,hb.isPublic⟩
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) _ hp
  rcases minimum_pair_observation_form ns swap left right ns.restricted m hm he.symm with
    ⟨u,v,rfl⟩ | ⟨i,k,hk,rfl⟩
  · have hargs := (EqE.pair_iff _ _ _ _).mp he
    have hu := ha.least u hm.isPublic.1 hargs.1
    have hv := hb.least v hm.isPublic.2 hargs.2
    exact .of_minimal (hm.of_equivalent_size hp he (by simp only [Term.nodeCount]; omega))
  · have hargs := (pair_equality_iff_projections _ _ _
      (ballot_tail_pair_value ns swap left right i k hk)).mp he
    have hfirst := minimum_honest_field_match_transfer ns hf swap swap' left right a ha i k hk hargs.1
    have hrest := minimum_honest_tail_match_transfer ns hf swap swap' left right b hb i (k+1) (by omega)
      (by simpa only [Term.drop_succ_outer, Frame.eval, Term.subst] using hargs.2)
    refine ⟨_,hm,he,?_⟩
    apply (pair_equality_iff_projections _ _ _ (ballot_tail_pair_value ns swap' left right i k hk)).mpr
    exact ⟨hfirst,by simpa only [Term.drop_succ_outer, Frame.eval, Term.subst] using hrest⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {n : Nat}

/-- Root cases still requiring shared minimization after projection and pairing. -/
def CryptoArithmeticRootCase (φ : Frame restricted n) : Recipe n → Prop
  | .binary .dec a b => ∃ m, DecryptionMatch (φ.eval a) (φ.eval b) m
  | .ternary .checkspk a b c => ProofCheckMatch (φ.eval a) (φ.eval b) (φ.eval c)
  | .binary .mul _ _ | .binary .add _ _ | .binary .compose _ _ => True
  | .ternary .penc _ _ _ => True
  | _ => False

def CryptoArithmeticRootTransport (φ ψ : Frame restricted n) : Prop :=
  ∀ r, r.Public restricted → MinimumChildren φ r →
    ¬ MinimalRecipe restricted φ.value r → CryptoArithmeticRootCase φ r → SharedMinimum φ ψ r

end ExplainableCrypto.Helios.Symbolic.Frame

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Pairing is supplied by a theorem, leaving only cryptographic and arithmetic
root obligations in the previous nonprojection interface. -/
theorem nonprojection_transport_of_crypto_arithmetic (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty)
    (h : Frame.CryptoArithmeticRootTransport (frame ns swap left right) (frame ns swap' left right)) :
    Frame.NonprojectionRootTransport (frame ns swap left right) (frame ns swap' left right) := by
  intro r hp hc hm hcase
  cases r with
  | binary f a b =>
    cases f with
    | pair => exact minimum_children_pair_shared ns hf swap swap' left right a b hc.1 hc.2
    | mul | add | compose | dec | partialDecrypt => exact h _ hp hc hm hcase
  | unary f a => cases f <;> exact False.elim hcase
  | ternary f a b c => cases f <;> exact h _ hp hc hm hcase
  | name | var | const | spk => exact h _ hp hc hm hcase

/-- The remaining premises cover successful decryption/checking, ciphertext
construction and arithmetic in both orientations. They remain unproved here. -/
theorem staticEq_of_crypto_arithmetic_transport (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty)
    (hforward : Frame.CryptoArithmeticRootTransport (frame ns false left right) (frame ns true left right))
    (hreverse : Frame.CryptoArithmeticRootTransport (frame ns true left right) (frame ns false left right)) :
    Frame.StaticEq (frame ns false left right) (frame ns true left right) :=
  staticEq_of_nonprojection_transport ns hf left right
    (nonprojection_transport_of_crypto_arithmetic ns hf false true left right hforward)
    (nonprojection_transport_of_crypto_arithmetic ns hf true false left right hreverse)

end ExplainableCrypto.Helios.Symbolic.Historical.General
