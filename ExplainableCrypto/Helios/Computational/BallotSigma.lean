import ExplainableCrypto.Helios.Computational.StrongBallot
import Examples.Schnorr.SigmaProtocol

/-! The actual disjunctive Chaum–Pedersen protocol as a VCVio Σ-protocol.
Responses contain c₀,z₀,z₁; c₁ is reconstructed as c-c₀. All statement fields
remain explicit so the subsequent strong Fiat–Shamir hash can bind them.
The historical instance uses nonzero proof coins; a sampler parameter exposes
only the reference distribution needed for the later statistical HVZK bridge. -/

namespace ExplainableCrypto.Helios.Computational

open OracleComp
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

structure BallotStatement (G : Type) where
  generator : G
  publicKey : G
  ciphertext : Ciphertext G
  deriving DecidableEq

abbrev BallotWitness (F : Type) := Bool × F
abbrev BallotCommitment (G : Type) := (G × G) × (G × G)
abbrev BallotResponse (F : Type) := F × F × F
abbrev BallotPrivateCoins (F : Type) := F × F × F

def BallotStatement.Witnesses (stmt : BallotStatement G) (wit : BallotWitness F) : Prop :=
  stmt.ciphertext = encryptWith stmt.generator stmt.publicKey wit.2 (voteScalar wit.1)

def ballotTranscriptProof (pc : BallotCommitment G) (challenge : F) (resp : BallotResponse F) :
    Proof01 F G :=
  ⟨⟨pc.1.1, pc.1.2, resp.1, resp.2.1⟩, ⟨pc.2.1, pc.2.2, challenge - resp.1, resp.2.2⟩⟩

def ballotCommitWith (stmt : BallotStatement G) (wit : BallotWitness F)
    (coins : BallotPrivateCoins F) : BallotCommitment G :=
  let simulated := simulatedBranch stmt.generator stmt.publicKey stmt.ciphertext
    (voteScalar (!wit.1)) coins.2.1 coins.2.2
  let real := (coins.1 • stmt.generator, coins.1 • stmt.publicKey)
  if wit.1 then ((simulated.a, simulated.b), real) else (real, (simulated.a, simulated.b))

def ballotRespondWith (wit : BallotWitness F) (coins : BallotPrivateCoins F)
    (challenge : F) : BallotResponse F :=
  let realChallenge := challenge - coins.2.1
  let realResponse := coins.1 + wit.2 * realChallenge
  if wit.1 then (coins.2.1, coins.2.2, realResponse)
  else (realChallenge, realResponse, coins.2.2)

def ballotExtract [DecidableEq F] (challenge₁ : F) (resp₁ : BallotResponse F)
    (challenge₂ : F) (resp₂ : BallotResponse F) : BallotWitness F :=
  if resp₁.1 ≠ resp₂.1 then (false, (resp₁.2.1 - resp₂.2.1) * (resp₁.1 - resp₂.1)⁻¹)
  else (true, (resp₁.2.2 - resp₂.2.2) *
    ((challenge₁ - resp₁.1) - (challenge₂ - resp₂.1))⁻¹)

/-- A single branch is Schnorr over the product group `(g,pk)`. Recovering its
exponent gives both ciphertext equations, including the plaintext offset. -/
theorem Branch.extract_ciphertext (g pk : G) (ct : Ciphertext G) (m : F)
    (p q : Branch F G) (ha : p.a = q.a) (hb : p.b = q.b)
    (hc : p.challenge ≠ q.challenge) (hp : p.Valid g pk ct m) (hq : q.Valid g pk ct m) :
    ct = encryptWith g pk ((p.response - q.response) * (p.challenge - q.challenge)⁻¹) m := by
  have hn : p.challenge - q.challenge ≠ 0 := sub_ne_zero.mpr hc
  have extract_eq (base value : G) (a b : G) (hab : a = b)
      (h₁ : p.response • base = a + p.challenge • value)
      (h₂ : q.response • base = b + q.challenge • value) :
      ((p.response - q.response) * (p.challenge - q.challenge)⁻¹) • base = value := by
    have hs : (p.response - q.response) • base = (p.challenge - q.challenge) • value := by
      rw [sub_smul, sub_smul, h₁, h₂, hab, add_sub_add_left_eq_sub]
    calc
      _ = (p.challenge - q.challenge)⁻¹ • ((p.response - q.response) • base) := by
        rw [mul_comm, mul_smul]
      _ = (p.challenge - q.challenge)⁻¹ • ((p.challenge - q.challenge) • value) := by rw [hs]
      _ = value := by rw [← mul_smul, inv_mul_cancel₀ hn, one_smul]
  have hfirst := extract_eq g ct.1 p.a q.a ha hp.1 hq.1
  have hsecond := extract_eq pk (ct.2 - m • g) p.b q.b hb hp.2 hq.2
  apply Prod.ext
  · exact hfirst.symm
  · change ct.2 = m • g + _
    rw [hsecond]
    abel

theorem ballotExtract_valid [DecidableEq F] (stmt : BallotStatement G)
    (pc : BallotCommitment G) (c₁ c₂ : F) (p₁ p₂ : BallotResponse F) (hc : c₁ ≠ c₂)
    (h₁ : (ballotTranscriptProof pc c₁ p₁).Valid (fun _ => c₁) stmt.generator stmt.publicKey stmt.ciphertext)
    (h₂ : (ballotTranscriptProof pc c₂ p₂).Valid (fun _ => c₂) stmt.generator stmt.publicKey stmt.ciphertext) :
    stmt.Witnesses (ballotExtract c₁ p₁ c₂ p₂) := by
  unfold ballotExtract
  split
  · next he =>
      exact Branch.extract_ciphertext stmt.generator stmt.publicKey stmt.ciphertext 0
        (ballotTranscriptProof pc c₁ p₁).zero (ballotTranscriptProof pc c₂ p₂).zero
        rfl rfl he h₁.1 h₂.1
  · next he =>
      have hp : p₁.1 = p₂.1 := not_ne_iff.mp he
      have hd : c₁ - p₁.1 ≠ c₂ - p₂.1 := by
        rw [hp]
        intro h
        apply hc
        simpa using congrArg (fun x => x + p₂.1) h
      exact Branch.extract_ciphertext stmt.generator stmt.publicKey stmt.ciphertext 1
        (ballotTranscriptProof pc c₁ p₁).one (ballotTranscriptProof pc c₂ p₂).one
        rfl rfl hd h₁.2.1 h₂.2.1

theorem ballotTranscript_honest_valid (stmt : BallotStatement G) (wit : BallotWitness F)
    (coins : BallotPrivateCoins F) (challenge : F) (hw : stmt.Witnesses wit) :
    (ballotTranscriptProof (ballotCommitWith stmt wit coins) challenge
      (ballotRespondWith wit coins challenge)).Valid (fun _ => challenge)
      stmt.generator stmt.publicKey stmt.ciphertext := by
  rcases stmt with ⟨g, pk, ct⟩
  rcases wit with ⟨vote, nonce⟩
  change ct = encryptWith g pk nonce (voteScalar vote) at hw
  subst ct
  cases vote
  · simpa [ballotTranscriptProof, ballotCommitWith, ballotRespondWith, proveVote, proveZero,
      realBranch, simulatedBranch, voteScalar] using
      proveZero_valid (fun _ => challenge) g pk nonce coins.1 coins.2.1 coins.2.2
  · simpa [ballotTranscriptProof, ballotCommitWith, ballotRespondWith, proveVote, proveOne,
      realBranch, simulatedBranch, voteScalar] using
      proveOne_valid (fun _ => challenge) g pk nonce coins.1 coins.2.1 coins.2.2

theorem ballotTranscript_strongProveVote (hash : StatementHash F G) (g pk : G)
    (vote : Bool) (nonce w e z : F) :
    let stmt : BallotStatement G := ⟨g, pk, encryptWith g pk nonce (voteScalar vote)⟩
    let pc := ballotCommitWith stmt (vote, nonce) (w,e,z)
    ballotTranscriptProof pc (hash g pk stmt.ciphertext pc)
      (ballotRespondWith (vote, nonce) (w,e,z) (hash g pk stmt.ciphertext pc)) =
        strongProveVote hash g pk vote nonce w e z := by
  cases vote <;> simp [ballotTranscriptProof, ballotCommitWith, ballotRespondWith,
    strongProveVote, proveVote, proveZero, proveOne, realBranch, simulatedBranch, voteScalar]

variable [DecidableEq F] [DecidableEq G]

instance (stmt : BallotStatement G) (wit : BallotWitness F) : Decidable (stmt.Witnesses wit) := by
  unfold BallotStatement.Witnesses
  infer_instance

local instance (hash : Hash F G) (g pk : G) (ct : Ciphertext G) (p : Proof01 F G) :
    Decidable (p.Valid hash g pk ct) := by
  unfold Proof01.Valid Branch.Valid
  infer_instance

def ballotSigmaWithSampler (sample : ProbComp F) :
    SigmaProtocol (BallotStatement G) (BallotWitness F) (BallotCommitment G)
      (BallotPrivateCoins F) F (BallotResponse F)
      (fun stmt wit => decide (stmt.Witnesses wit)) where
  commit stmt wit := do
    let w ← sample
    let e ← sample
    let z ← sample
    pure (ballotCommitWith stmt wit (w,e,z), (w,e,z))
  respond _ wit coins challenge := pure (ballotRespondWith wit coins challenge)
  verify stmt pc challenge resp := decide ((ballotTranscriptProof pc challenge resp).Valid
    (fun _ => challenge) stmt.generator stmt.publicKey stmt.ciphertext)
  sim stmt := do
    let c ← sample
    let e ← sample
    let z₀ ← sample
    let z₁ ← sample
    let p₀ := simulatedBranch stmt.generator stmt.publicKey stmt.ciphertext 0 e z₀
    let p₁ := simulatedBranch stmt.generator stmt.publicKey stmt.ciphertext 1 (c-e) z₁
    pure ((p₀.a, p₀.b), (p₁.a, p₁.b))
  extract c₁ p₁ c₂ p₂ := pure (ballotExtract c₁ p₁ c₂ p₂)

noncomputable def ballotSigma [Fintype F] := ballotSigmaWithSampler (G := G) (sampleNonzero F)

theorem ballotSigmaWithSampler_speciallySound (sample : ProbComp F) :
    (ballotSigmaWithSampler (G := G) sample).SpeciallySound := by
  intro stmt pc c₁ c₂ p₁ p₂ hc h₁ h₂ wit hw
  simp only [ballotSigmaWithSampler, support_pure, Set.mem_singleton_iff] at hw
  subst wit
  simp only [ballotSigmaWithSampler, decide_eq_true_eq] at h₁ h₂ ⊢
  exact ballotExtract_valid stmt pc c₁ c₂ p₁ p₂ hc h₁ h₂

theorem ballotSigma_speciallySound [Fintype F] : (ballotSigma (F := F) (G := G)).SpeciallySound :=
  ballotSigmaWithSampler_speciallySound _

theorem ballotSigmaWithSampler_complete [SampleableType F] (sample : ProbComp F) : (ballotSigmaWithSampler (G := G) sample).PerfectlyComplete := by
  intro stmt wit hw
  have hv := fun coins challenge => ballotTranscript_honest_valid stmt wit coins challenge
    (of_decide_eq_true hw)
  simp only [ballotSigmaWithSampler, monad_norm]
  simp [hv]

theorem ballotSigma_complete [Fintype F] [SampleableType F] :
    (ballotSigma (F := F) (G := G)).PerfectlyComplete :=
  ballotSigmaWithSampler_complete _

#print axioms ballotTranscript_strongProveVote
#print axioms ballotSigma_complete
#print axioms Branch.extract_ciphertext
#print axioms ballotExtract_valid
#print axioms ballotTranscript_honest_valid
#print axioms ballotSigma_speciallySound

end ExplainableCrypto.Helios.Computational
