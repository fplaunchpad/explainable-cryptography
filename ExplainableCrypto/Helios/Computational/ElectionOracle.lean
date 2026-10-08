import ExplainableCrypto.Helios.Computational.RepairedExecution
import ExplainableCrypto.Helios.Computational.RepairedBoardOracle
import ExplainableCrypto.Helios.Computational.RepairedGame

/-! One oracle interface for the existing separate statement-bound proof hashes.
Fixed-function interpretation preserves the original complete public execution.
This is a protocol interface, not an efficient-attacker or secrecy theorem. -/
namespace ExplainableCrypto.Helios.Computational.ElectionOracle
open OracleComp OracleSpec

inductive Key (G : Type) where
  | ballot (statement : BallotStatement G) (commitment : BallotCommitment G)
  | key (generator publicKey commitment : G)
  | decryption (generator publicKey : G) (ciphertext : Ciphertext G)
      (share : G) (commitment : G × G)
  deriving DecidableEq

abbrev HashSpec (F G : Type) := Key G →ₒ F
abbrev Spec (F G : Type) := unifSpec + HashSpec F G
abbrev Comp (F G : Type) := OracleComp (Spec F G)
abbrev Cache (F G : Type) := (HashSpec F G).QueryCache

def ask {F G : Type} (key : Key G) : Comp F G F :=
  liftM ((Spec F G).query (.inr key))

def ballotImpl (F G : Type) : QueryImpl (BallotOracleSpec F G) (Comp F G) :=
  fun t => match t with
    | .inl n => liftM ((Spec F G).query (.inl n))
    | .inr k => ask (.ballot k.1 k.2)

def liftBallot {F G A : Type} (oa : BallotOracleComp F G A) : Comp F G A :=
  simulateQ (ballotImpl F G) oa

def functionImpl {F G : Type} (hashes : StrongCryptoHashes F G) : QueryImpl (Spec F G) ProbComp :=
  fun t => match t with
    | .inl n => liftM (unifSpec.query n)
    | .inr k => pure (match k with
      | .ballot s c => hashes.ballot s.generator s.publicKey s.ciphertext c
      | .key g pk c => hashes.key g pk c
      | .decryption g pk ct share c => hashes.decryption g pk ct share c)

theorem ask_function {F G : Type} (hashes : StrongCryptoHashes F G) (k : Key G) :
    simulateQ (functionImpl hashes) (ask k) = pure (match k with
      | .ballot s c => hashes.ballot s.generator s.publicKey s.ciphertext c
      | .key g pk c => hashes.key g pk c
      | .decryption g pk ct share c => hashes.decryption g pk ct share c) := by
  simp [ask,functionImpl]

theorem liftBallot_function {F G A : Type} (hashes : StrongCryptoHashes F G)
    (oa : BallotOracleComp F G A) :
    simulateQ (functionImpl hashes) (liftBallot oa) =
      simulateQ (ballotFunctionImpl hashes.ballot) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [liftBallot]
  | query_bind t next ih =>
    simp only [liftBallot,simulateQ_bind] at *
    have hq : simulateQ (functionImpl hashes)
        (simulateQ (ballotImpl F G) (liftM ((BallotOracleSpec F G).query t))) =
        simulateQ (ballotFunctionImpl hashes.ballot) (liftM ((BallotOracleSpec F G).query t)) := by
      cases t with
      | inl n => simp [ballotImpl,functionImpl,ballotFunctionImpl]
      | inr k => simp [ballotImpl,ask_function,ballotFunctionImpl]
    rw [hq]
    exact bind_congr ih

def liftProb {F G A : Type} (oa : ProbComp A) : Comp F G A :=
  OracleComp.liftComp oa (Spec F G)

theorem liftProb_function {F G A : Type} (hashes : StrongCryptoHashes F G) (oa : ProbComp A) :
    simulateQ (functionImpl hashes) (liftProb oa) = oa := by
  unfold liftProb
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply (functionImpl hashes)
    (QueryImpl.id' unifSpec) (fun _ => rfl)]
  exact simulateQ_id' oa

/-- The original two public interaction points, with proof-oracle access. -/
structure Adversary (F G State : Type) where
  castBallot : PublicPrefix F G → Comp F G (Ballot F G 2 × State)
  guessVote : State → PublicResult F G → Comp F G Bool

def Adversary.interpret {F G State : Type} (hashes : StrongCryptoHashes F G)
    (adversary : Adversary F G State) : BallotAdversary F G State where
  castBallot before := simulateQ (functionImpl hashes) (adversary.castBallot before)
  guessVote saved view := simulateQ (functionImpl hashes) (adversary.guessVote saved view)

def Adversary.ofOriginal {F G State : Type} (adversary : BallotAdversary F G State) :
    Adversary F G State where
  castBallot before := liftProb (adversary.castBallot before)
  guessVote saved view := liftProb (adversary.guessVote saved view)

theorem Adversary.interpret_ofOriginal {F G State : Type} (hashes : StrongCryptoHashes F G)
    (adversary : BallotAdversary F G State) :
    (ofOriginal adversary).interpret hashes = adversary := by
  cases adversary
  simp [interpret,ofOriginal,liftProb_function]

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

def keyWithCoins (g : G) (secret nonce : F) : Comp F G (SchnorrProof F G) := do
  let commitment := nonce • g
  let c ← ask (.key g (secret • g) commitment)
  pure ⟨commitment,nonce+c*secret⟩

def partialWithCoins (g : G) (secret nonce : F) (ct : Ciphertext G) :
    Comp F G (SchnorrProof F (G × G)) := do
  let commitment := (nonce • g,nonce • ct.1)
  let c ← ask (.decryption g (secret • g) ct (partialDecrypt secret ct) commitment)
  pure ⟨commitment,nonce+c*secret⟩

theorem keyWithCoins_function (hashes : StrongCryptoHashes F G) (g : G) (secret nonce : F) :
    simulateQ (functionImpl hashes) (keyWithCoins g secret nonce) =
      pure (strongKeyProof hashes g secret nonce) := by
  simp [keyWithCoins,ask_function,strongKeyProof,schnorrProof]

theorem partialWithCoins_function (hashes : StrongCryptoHashes F G) (g : G)
    (secret nonce : F) (ct : Ciphertext G) :
    simulateQ (functionImpl hashes) (partialWithCoins g secret nonce ct) =
      pure (strongPartialProof hashes g secret nonce ct) := by
  simp [partialWithCoins,ask_function,strongPartialProof,partialProof,schnorrProof]

variable [DecidableEq F] [DecidableEq G]

def prefixWithCoins (fingerprint : PublicParameters F G → Nat) (g : G)
    (secret keyNonce : F) (vote : Bool) (alice bob : HonestCoins F) : Comp F G (PublicPrefix F G) := do
  let keyProof ← keyWithCoins g secret keyNonce
  let parameters : PublicParameters F G := ⟨g,secret • g,keyProof,[0,1],[0,1,2]⟩
  let cast ← liftBallot (repairedCastHonestPairWithCoinsOracle g (secret • g) vote alice bob)
  pure ⟨parameters,fingerprint parameters,cast.1,cast.2⟩

def finishWithCoins (secret : F) (nonces : Fin 2 → F) (before : PublicPrefix F G)
    (submission : Ballot F G 2) : Comp F G (PublicResult F G) := do
  let g := before.parameters.generator
  let cast ← liftBallot (repairedSubmitOracle g before.parameters.publicKey 2 before.board submission)
  let encrypted := boardTally cast.2
  let shares := fun j => partialDecrypt secret (encrypted j)
  let proof0 ← partialWithCoins g secret (nonces 0) (encrypted 0)
  let proof1 ← partialWithCoins g secret (nonces 1) (encrypted 1)
  pure ⟨before,submission,cast.1,cast.2,encrypted,shares,![proof0,proof1],
    fun j => decodeBounded (F := F) g cast.2.length (decryptWithPartial (encrypted j) (shares j))⟩

/-- The key proof, fingerprint, honest decisions and exact retained board agree. -/
theorem prefix_function (hashes : StrongCryptoHashes F G) (g : G)
    (secret keyNonce : F) (vote : Bool) (alice bob : HonestCoins F) :
    simulateQ (functionImpl hashes) (prefixWithCoins hashes.fingerprint g secret keyNonce vote alice bob) =
      pure (makeRepairedPrefix hashes g secret keyNonce vote alice bob) := by
  simp [prefixWithCoins,keyWithCoins_function,liftBallot_function,
    repairedCastHonestPairWithCoinsOracle_function,makeRepairedPrefix]

/-- Complete public result agreement includes rejection, board, tally, shares,
trustee proofs and bounded decoding failure, not just tally equality. -/
theorem finish_function (hashes : StrongCryptoHashes F G) (secret : F)
    (nonces : Fin 2 → F) (before : PublicPrefix F G) (submission : Ballot F G 2) :
    simulateQ (functionImpl hashes) (finishWithCoins secret nonces before submission) =
      pure (finishRepairedElection hashes secret nonces before submission) := by
  simp only [finishWithCoins,simulateQ_bind,liftBallot_function,repairedSubmitOracle_function,
    pure_bind,partialWithCoins_function,simulateQ_pure]
  unfold finishRepairedElection
  congr 2
  funext j
  fin_cases j <;> rfl

variable [Fintype F]

noncomputable def world {State : Type} (fingerprint : PublicParameters F G → Nat) (g : G)
    (adversary : Adversary F G State) (vote : Bool) : Comp F G Bool := do
  let secret ← liftProb (sampleNonzero F)
  let keyNonce ← liftProb (sampleNonzero F)
  let decryptionNonces ← liftProb (drawNoncePair F)
  let pair ← liftProb (drawHonestPair F)
  let before ← prefixWithCoins fingerprint g secret keyNonce vote pair.1 pair.2
  let (submission,saved) ← adversary.castBallot before
  let view ← finishWithCoins secret ![decryptionNonces.1,decryptionNonces.2] before submission
  adversary.guessVote saved view

noncomputable def game {State : Type} (fingerprint : PublicParameters F G → Nat) (g : G)
    (adversary : Adversary F G State) : Comp F G Bool := do
  let vote ← liftProb (uniformSample Bool)
  let guess ← world fingerprint g adversary vote
  pure (decide (guess = vote))

/-- Exact original sampled world, including stateful oracle attacker callbacks. -/
theorem world_function {State : Type} (hashes : StrongCryptoHashes F G) (g : G)
    (adversary : Adversary F G State) (vote : Bool) :
    simulateQ (functionImpl hashes) (world hashes.fingerprint g adversary vote) =
      repairedBallotWorld hashes g (adversary.interpret hashes) vote := by
  simp [world,repairedBallotWorld,simulateQ_bind,liftProb_function,prefix_function,
    finish_function,Adversary.interpret]

theorem game_function {State : Type} (hashes : StrongCryptoHashes F G) (g : G)
    (adversary : Adversary F G State) :
    simulateQ (functionImpl hashes) (game hashes.fingerprint g adversary) =
      repairedBallotSecrecyGame hashes g (adversary.interpret hashes) := by
  simp [game,repairedBallotSecrecyGame,liftProb_function,world_function]

/-- Preparation can query before any election randomness or protocol hash.
Its private result selects the subsequent attacker callbacks. -/
noncomputable def preparedGame {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G State) : Comp F G Bool := do
  let initial ← prepare
  game fingerprint g (adversary initial)

theorem preparedGame_function {Init State : Type} (hashes : StrongCryptoHashes F G)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G State) :
    simulateQ (functionImpl hashes) (preparedGame hashes.fingerprint g prepare adversary) =
      (do let initial ← simulateQ (functionImpl hashes) prepare
          repairedBallotSecrecyGame hashes g ((adversary initial).interpret hashes)) := by
  simp [preparedGame,game_function]

variable [SampleableType F]

def randomImpl : QueryImpl (Spec F G) (StateT (Cache F G) ProbComp) :=
  QueryImpl.ofLift unifSpec (StateT (Cache F G) ProbComp) +
    (@OracleSpec.randomOracle (Key G) inferInstance (HashSpec F G) (fun _ => ‹SampleableType F›))

def run {A : Type} (oa : Comp F G A) (cache : Cache F G) : ProbComp (A × Cache F G) :=
  (simulateQ randomImpl oa).run cache

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [Fintype F] in
/-- Every continuation sees the actual shared successor cache. -/
theorem run_bind {A B : Type} (oa : Comp F G A) (next : A → Comp F G B) (cache : Cache F G) :
    run (oa >>= next) cache = (do let out ← run oa cache; run (next out.1) out.2) := by
  simp [run,simulateQ_bind,StateT.run_bind]

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [Fintype F] in
/-- All proof types use one lazy cache indexed by their full original arguments. -/
theorem run_ask (k : Key G) (cache : Cache F G) :
    run (ask k) cache = (match cache k with
      | some c => pure (c,cache)
      | none => do let c ← uniformSample F; pure (c,cache.cacheQuery k c)) := by
  simp only [run,ask,simulateQ_spec_query,randomImpl,QueryImpl.add_apply_inr,randomOracle.run_eq]
  cases cache k <;> rfl

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [Fintype F] in
theorem run_pure {A : Type} (a : A) (cache : Cache F G) :
    run (pure a : Comp F G A) cache = pure (a,cache) := by
  simp [run]

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [Fintype F] in
theorem run_repeat (k : Key G) (cache : Cache F G) :
    run (do let c ← ask k; let d ← ask k; pure (c,d)) cache =
      (do let out ← run (ask k) cache; pure ((out.1,out.1),out.2)) := by
  cases h : cache k <;> simp only [run_bind,run_ask,h,pure_bind,
    QueryCache.cacheQuery_self,run_pure,bind_assoc]

/-- Pre-election answers are retained for casting, protocol verification and
post-tally guessing by executing the entire game under one state handler. -/
theorem run_preparedGame {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G State)
    (cache : Cache F G) :
    run (preparedGame fingerprint g prepare adversary) cache =
      (do let initial ← run prepare cache
          run (game fingerprint g (adversary initial.1)) initial.2) := by
  exact run_bind prepare (fun initial => game fingerprint g (adversary initial)) cache

/-- The oracle cache is challenger-local. Only protocol publications passed to
the callbacks are visible; the outer experiment returns the winning bit. -/
noncomputable def randomGame {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G State) : ProbComp Bool :=
  Prod.fst <$> run (preparedGame fingerprint g prepare adversary) (fun _ => none)

#print axioms ask_function
#print axioms liftBallot_function
#print axioms keyWithCoins_function
#print axioms partialWithCoins_function
#print axioms prefix_function
#print axioms finish_function
#print axioms run_bind
#print axioms run_ask
#print axioms liftProb_function
#print axioms Adversary.interpret_ofOriginal
#print axioms world_function
#print axioms game_function
#print axioms preparedGame_function
#print axioms run_pure
#print axioms run_repeat
#print axioms run_preparedGame
end ExplainableCrypto.Helios.Computational.ElectionOracle
