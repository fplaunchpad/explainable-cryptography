import ExplainableCrypto.Helios.Symbolic.AdditionMinimumClosure

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {n : Nat}

/-- The local obligations left after addition: successful decryption/checking
and multiplication. -/
def DecryptCheckMulCase (φ : Frame restricted n) : Recipe n → Prop
  | .binary .dec a b => ∃ m, DecryptionMatch (φ.eval a) (φ.eval b) m
  | .ternary .checkspk a b c => ProofCheckMatch (φ.eval a) (φ.eval b) (φ.eval c)
  | .binary .mul _ _ => True
  | _ => False

def DecryptCheckMulTransport (φ ψ : Frame restricted n) : Prop :=
  ∀ r, r.Public restricted → MinimumChildren φ r →
    ¬ MinimalRecipe restricted φ.value r → DecryptCheckMulCase φ r → SharedMinimum φ ψ r

end ExplainableCrypto.Helios.Symbolic.Frame

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Addition uses a minimum raw-E0 representative, shared before substitution. -/
theorem four_case_transport_of_three_cases (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty)
    (h : Frame.DecryptCheckMulTransport (frame ns swap left right) (frame ns swap' left right)) :
    Frame.DecryptCheckAddMulTransport (frame ns swap left right) (frame ns swap' left right) := by
  intro r hp hc hm hcase
  cases r with
  | binary f a b =>
    cases f with
    | add => exact minimum_children_add_shared ns swap left right a b hc.1 hc.2 _
    | pair | mul | compose | partialDecrypt | dec => exact h _ hp hc hm hcase
  | ternary f a b c => cases f <;> exact h _ hp hc hm hcase
  | unary f a => cases f <;> exact False.elim hcase
  | name | var | const | spk => exact h _ hp hc hm hcase

/-- Static equivalence still requires successful decryption/checking and
multiplication transport in both orientations. Those premises remain explicit. -/
theorem staticEq_of_decrypt_check_mul_transport (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty)
    (hforward : Frame.DecryptCheckMulTransport (frame ns false left right) (frame ns true left right))
    (hreverse : Frame.DecryptCheckMulTransport (frame ns true left right) (frame ns false left right)) :
    Frame.StaticEq (frame ns false left right) (frame ns true left right) :=
  staticEq_of_decrypt_check_add_mul_transport ns hf left right
    (four_case_transport_of_three_cases ns false true left right hforward)
    (four_case_transport_of_three_cases ns true false left right hreverse)

end ExplainableCrypto.Helios.Symbolic.Historical.General
