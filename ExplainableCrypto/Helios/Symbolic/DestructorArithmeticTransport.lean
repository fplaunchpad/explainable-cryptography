import ExplainableCrypto.Helios.Symbolic.ConstructedCiphertextMinima

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {n : Nat}

/-- Remaining local cases after closure of every passive constructor and
projection: successful decryption/checking and arithmetic roots. -/
def DestructorArithmeticRootCase (φ : Frame restricted n) : Recipe n → Prop
  | .binary .dec a b => ∃ m, DecryptionMatch (φ.eval a) (φ.eval b) m
  | .ternary .checkspk a b c => ProofCheckMatch (φ.eval a) (φ.eval b) (φ.eval c)
  | .binary .mul _ _ | .binary .add _ _ | .binary .compose _ _ => True
  | _ => False

def DestructorArithmeticRootTransport (φ ψ : Frame restricted n) : Prop :=
  ∀ r, r.Public restricted → MinimumChildren φ r →
    ¬ MinimalRecipe restricted φ.value r → DestructorArithmeticRootCase φ r → SharedMinimum φ ψ r

end ExplainableCrypto.Helios.Symbolic.Frame

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Constructed ciphertext closure discharges penc without freshness. -/
theorem crypto_transport_of_destructor_arithmetic (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty)
    (h : Frame.DestructorArithmeticRootTransport (frame ns swap left right) (frame ns swap' left right)) :
    Frame.CryptoArithmeticRootTransport (frame ns swap left right) (frame ns swap' left right) := by
  intro r hp hc hm hcase
  cases r with
  | ternary f a b c =>
    cases f with
    | penc => exact False.elim (hm (minimum_penc_of_children ns swap left right a b c hc.1 hc.2.1 hc.2.2))
    | checkspk => exact h _ hp hc hm hcase
  | binary f a b => cases f <;> exact h _ hp hc hm hcase
  | unary f a => cases f <;> exact False.elim hcase
  | name | var | const | spk => exact h _ hp hc hm hcase

/-- Initial-frame static equivalence follows if the remaining successful
destructor and arithmetic roots have shared minima in both orientations. -/
theorem staticEq_of_destructor_arithmetic_transport (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty)
    (hforward : Frame.DestructorArithmeticRootTransport (frame ns false left right) (frame ns true left right))
    (hreverse : Frame.DestructorArithmeticRootTransport (frame ns true left right) (frame ns false left right)) :
    Frame.StaticEq (frame ns false left right) (frame ns true left right) :=
  staticEq_of_crypto_arithmetic_transport ns hf left right
    (crypto_transport_of_destructor_arithmetic ns false true left right hforward)
    (crypto_transport_of_destructor_arithmetic ns true false left right hreverse)

end ExplainableCrypto.Helios.Symbolic.Historical.General
