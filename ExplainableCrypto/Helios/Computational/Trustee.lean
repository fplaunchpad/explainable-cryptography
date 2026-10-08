import ExplainableCrypto.Helios.Computational.BallotProof
import Examples.Schnorr.SigmaProtocol

/-! Historical trustee transcripts (Smyth Appendix A). Equality of logarithms
is the same Schnorr equation over a product group. Hashes cover commitments;
this does not import a Fiat–Shamir security claim or change honest sampling. -/

namespace ExplainableCrypto.Helios.Computational

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

structure SchnorrProof (F G : Type) where
  commitment : G
  response : F

def schnorrProof (hash : G → F) (g : G) (secret nonce : F) : SchnorrProof F G :=
  ⟨nonce • g, nonce + hash (nonce • g) * secret⟩

def SchnorrProof.Valid (hash : G → F) (g key : G) (p : SchnorrProof F G) : Prop :=
  p.response • g = p.commitment + hash p.commitment • key

theorem schnorrProof_valid (hash : G → F) (g : G) (secret nonce : F) :
    (schnorrProof hash g secret nonce).Valid hash g (secret • g) := by
  simp [SchnorrProof.Valid, schnorrProof, add_smul, mul_smul]

/-- The historical deterministic response is VCVio's Schnorr response. -/
theorem schnorrProof_respond_vcvio [Fintype F] [DecidableEq F] [SampleableType F]
    [SampleableType G] [DecidableEq G] (hash : G → F) (g : G) (secret nonce : F) :
    (Schnorr.sigma F G g).respond (secret • g) secret nonce (hash (nonce • g)) =
      pure (schnorrProof hash g secret nonce).response := rfl

theorem schnorrProof_verify_vcvio [Fintype F] [DecidableEq F] [SampleableType F]
    [SampleableType G] [DecidableEq G] (hash : G → F) (g key : G) (p : SchnorrProof F G) :
    (Schnorr.sigma F G g).verify key p.commitment (hash p.commitment) p.response =
      decide (p.response • g = p.commitment + hash p.commitment • key) := rfl

def partialDecrypt (secret : F) (ct : Ciphertext G) : G := secret • ct.1

def partialProof (hash : (G × G) → F) (g : G) (secret nonce : F)
    (ct : Ciphertext G) : SchnorrProof F (G × G) :=
  schnorrProof hash (g, ct.1) secret nonce

theorem partialProof_valid (hash : (G × G) → F) (g : G) (secret nonce : F)
    (ct : Ciphertext G) :
    (partialProof hash g secret nonce ct).Valid hash (g, ct.1)
      (secret • g, partialDecrypt secret ct) :=
  schnorrProof_valid hash (g, ct.1) secret nonce

def decryptWithPartial (ct : Ciphertext G) (share : G) : G := ct.2 - share

theorem decryptWithPartial_correct (g : G) (secret nonce message : F) :
    decryptWithPartial (encryptWith g (secret • g) nonce message)
      (partialDecrypt secret (encryptWith g (secret • g) nonce message)) = message • g := by
  simp [decryptWithPartial, partialDecrypt, encryptWith, smul_smul, mul_comm]

theorem decryptWithPartial_vcvio [Fintype F] [DecidableEq F] [SampleableType F]
    [SampleableType G] (g : G) (secret : F) (ct : Ciphertext G) :
    (elGamalAsymmEnc F G g).decrypt secret ct =
      pure (some (decryptWithPartial ct (partialDecrypt secret ct))) := rfl

#print axioms schnorrProof_valid
#print axioms schnorrProof_respond_vcvio
#print axioms schnorrProof_verify_vcvio
#print axioms partialProof_valid
#print axioms decryptWithPartial_correct
#print axioms decryptWithPartial_vcvio

end ExplainableCrypto.Helios.Computational
