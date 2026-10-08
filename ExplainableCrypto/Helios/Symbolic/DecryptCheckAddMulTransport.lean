import ExplainableCrypto.Helios.Symbolic.CompositionMinimumClosure

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {n : Nat}

/-- Only successful decryption/checking, addition and multiplication remain. -/
def DecryptCheckAddMulCase (φ : Frame restricted n) : Recipe n → Prop
  | .binary .dec a b => ∃ m, DecryptionMatch (φ.eval a) (φ.eval b) m
  | .ternary .checkspk a b c => ProofCheckMatch (φ.eval a) (φ.eval b) (φ.eval c)
  | .binary .mul _ _ | .binary .add _ _ => True
  | _ => False

def DecryptCheckAddMulTransport (φ ψ : Frame restricted n) : Prop :=
  ∀ r, r.Public restricted → MinimumChildren φ r →
    ¬ MinimalRecipe restricted φ.value r → DecryptCheckAddMulCase φ r → SharedMinimum φ ψ r

end ExplainableCrypto.Helios.Symbolic.Frame

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Composition minimum-parent closure discharges its former local obligation. -/
theorem destructor_arithmetic_transport_of_four_cases (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty)
    (h : Frame.DecryptCheckAddMulTransport (frame ns swap left right) (frame ns swap' left right)) :
    Frame.DestructorArithmeticRootTransport (frame ns swap left right) (frame ns swap' left right) := by
  intro r hp hc hm hcase
  cases r with
  | binary f a b =>
    cases f with
    | compose => exact False.elim (hm (minimum_compose_of_children ns swap left right ns.restricted a b hc.1 hc.2))
    | pair | mul | add | partialDecrypt | dec => exact h _ hp hc hm hcase
  | ternary f a b c => cases f <;> exact h _ hp hc hm hcase
  | unary f a => cases f <;> exact False.elim hcase
  | name | var | const | spk => exact h _ hp hc hm hcase

/-- Static equivalence still requires all four remaining cases in both
orientations. The theorem does not assert either different-vote premise. -/
theorem staticEq_of_decrypt_check_add_mul_transport (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty)
    (hforward : Frame.DecryptCheckAddMulTransport (frame ns false left right) (frame ns true left right))
    (hreverse : Frame.DecryptCheckAddMulTransport (frame ns true left right) (frame ns false left right)) :
    Frame.StaticEq (frame ns false left right) (frame ns true left right) :=
  staticEq_of_destructor_arithmetic_transport ns hf left right
    (destructor_arithmetic_transport_of_four_cases ns false true left right hforward)
    (destructor_arithmetic_transport_of_four_cases ns true false left right hreverse)

end ExplainableCrypto.Helios.Symbolic.Historical.General
