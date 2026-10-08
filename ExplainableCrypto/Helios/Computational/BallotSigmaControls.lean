import ExplainableCrypto.Helios.Computational.BallotSigma
import ExplainableCrypto.Helios.Computational.ExecutionControls

/-! Independent p=23, q=11 extraction controls for the real ballot relation.
The companion Python oracle exhausts both bits, all nonces and challenge pairs. -/

namespace ExplainableCrypto.Helios.Computational.BallotSigmaControls

abbrev Scalar := ZMod 11
open ExecutionControls (encode)

def statement (vote : Bool) : BallotStatement Scalar :=
  ⟨1, 3, encryptWith (F := Scalar) 1 3 3 (voteScalar vote)⟩

def coins : BallotPrivateCoins Scalar := (4,2,3)

def commitment (vote : Bool) := ballotCommitWith (statement vote) (vote, (3 : Scalar)) coins

def response (vote : Bool) (c : Scalar) := ballotRespondWith (vote, (3 : Scalar)) coins c

local instance (stmt : BallotStatement Scalar) (wit : BallotWitness Scalar) :
    Decidable (stmt.Witnesses wit) := by
  unfold BallotStatement.Witnesses
  infer_instance

local instance (hash : Hash Scalar Scalar) (g pk : Scalar) (ct : Ciphertext Scalar)
    (p : Proof01 Scalar Scalar) : Decidable (p.Valid hash g pk ct) := by
  unfold Proof01.Valid Branch.Valid
  infer_instance

theorem literal_zero_commitments_and_responses :
    ((encode (commitment false).1.1, encode (commitment false).1.2),
      (encode (commitment false).2.1, encode (commitment false).2.2)) = ((16,2),(3,16)) ∧
    response false 5 = (3,2,3) ∧ response false 6 = (4,5,3) := by
  norm_num [ballotExtract, response, ballotRespondWith, coins, BallotStatement.Witnesses,
    statement, encryptWith, voteScalar]
  all_goals decide

theorem both_branches_extract_the_actual_nonce :
    ballotExtract 5 (response false 5) 6 (response false 6) = (false, (3 : Scalar)) ∧
    ballotExtract 5 (response true 5) 6 (response true 6) = (true, (3 : Scalar)) ∧
    (statement false).Witnesses (ballotExtract 5 (response false 5) 6 (response false 6)) ∧
    (statement true).Witnesses (ballotExtract 5 (response true 5) 6 (response true 6)) := by
  norm_num [ballotExtract, response, ballotRespondWith, coins, BallotStatement.Witnesses,
    statement, encryptWith, voteScalar]
  all_goals decide

theorem same_challenge_does_not_extract :
    (ballotTranscriptProof (commitment false) 5 (response false 5)).Valid (fun _ => 5)
      1 3 (statement false).ciphertext ∧
    ballotExtract 5 (response false 5) 5 (response false 5) = (true, (0 : Scalar)) ∧
    ¬ (statement false).Witnesses (ballotExtract 5 (response false 5) 5 (response false 5)) := by
  norm_num [ballotExtract, response, ballotRespondWith, coins, BallotStatement.Witnesses,
    statement, encryptWith, voteScalar]
  all_goals decide

theorem changing_commitments_does_not_extract :
    let otherCoins : BallotPrivateCoins Scalar := (5,2,3)
    let pc := ballotCommitWith (statement false) (false, (3 : Scalar)) otherCoins
    let resp := ballotRespondWith (false, (3 : Scalar)) otherCoins 6
    (ballotTranscriptProof pc 6 resp).Valid (fun _ => 6) 1 3 (statement false).ciphertext ∧
      pc ≠ commitment false ∧
      ballotExtract 5 (response false 5) 6 resp = (false, (4 : Scalar)) ∧
      ¬ (statement false).Witnesses (ballotExtract 5 (response false 5) 6 resp) := by
  norm_num [ballotExtract, response, ballotRespondWith, coins, BallotStatement.Witnesses,
    statement, encryptWith, voteScalar]
  all_goals decide

#print axioms literal_zero_commitments_and_responses
#print axioms both_branches_extract_the_actual_nonce
#print axioms same_challenge_does_not_extract
#print axioms changing_commitments_does_not_extract

end ExplainableCrypto.Helios.Computational.BallotSigmaControls
