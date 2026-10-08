import ExplainableCrypto.Helios.Computational.BallotProofProvenance
import ExplainableCrypto.Helios.Computational.RepairControls

/-! Independent modulo-23 fixtures retain accepted submissions, cross-kind
weeding and a rejected honest ballot whose generated proof target can recur. -/
namespace ExplainableCrypto.Helios.Computational.BallotProofProvenanceControls
open OracleComp OracleSpec
open ExecutionControls (aliceCoins bobCoins encode)
open RepairControls (hashes Scalar)

def thirdCoins : HonestCoins Scalar := ⟨![6,9],fun _ => 4,fun _ => 2,fun _ => 3⟩
def rejectedBobCoins : HonestCoins Scalar := ⟨![4,2],fun _ => 4,fun _ => 2,fun _ => 3⟩
def crossKindCoins : HonestCoins Scalar := ⟨![3,4],fun _ => 4,fun _ => 2,fun _ => 3⟩

def acceptedPrefix := repairedCastHonestPair hashes.ballot (1 : Scalar) 3 false aliceCoins bobCoins
def rejectedPrefix := repairedCastHonestPair hashes.ballot (1 : Scalar) 3 false aliceCoins rejectedBobCoins

theorem fresh_third_ballot_accepted :
    acceptedPrefix.1 = (.accepted,.accepted) ∧
    (repairedSubmit hashes.ballot 1 3 2 acceptedPrefix.2
      (strongHonestBallot hashes.ballot 1 3 false thirdCoins)).1 = .accepted := by decide

theorem literal_third_ciphertexts :
    let b := strongHonestBallot hashes.ballot 1 3 false thirdCoins
    ((encode (b.ciphertext 0).1,encode (b.ciphertext 0).2),
      (encode (b.ciphertext 1).1,encode (b.ciphertext 1).2),
      (encode b.aggregate.1,encode b.aggregate.2)) = ((18,13),(6,9),(16,2)) := by decide

theorem cross_kind_copy_rejected :
    let b := strongHonestBallot hashes.ballot 1 3 false crossKindCoins
    b.FreshFor (acceptedPrefix.2.map BoardEntry.ballot) ∧
    b.ciphertext 0 = (strongHonestBallot hashes.ballot 1 3 false aliceCoins).aggregate ∧
    (repairedSubmit hashes.ballot 1 3 2 acceptedPrefix.2 b).1 = .reusedCiphertext := by decide

/-- Bob's generated first proof is absent from the accepted board; another
accepted ballot can have exactly that same complete proof target. -/
theorem rejected_honest_target_can_recur :
    let bob := strongHonestBallot hashes.ballot 1 3 true rejectedBobCoins
    let submission := strongHonestBallot hashes.ballot 1 3 true bobCoins
    rejectedPrefix.1 = (.accepted,.reusedCiphertext) ∧
    rejectedPrefix.2 = [⟨0,strongHonestBallot hashes.ballot 1 3 false aliceCoins⟩] ∧
    (repairedSubmit hashes.ballot 1 3 2 rejectedPrefix.2 submission).1 = .accepted ∧
    (submission.coveredStatement 1 3 (some 0),(submission.proof 0).commitment) =
      (bob.coveredStatement 1 3 (some 0),(bob.proof 0).commitment) ∧
    ∀ entry ∈ rejectedPrefix.2, ∀ i,
      bob.coveredStatement 1 3 (some 0) ≠ entry.ballot.coveredStatement 1 3 i := by
  dsimp only
  have hb : rejectedPrefix.2 = [⟨0,strongHonestBallot hashes.ballot 1 3 false aliceCoins⟩] := rfl
  refine ⟨by decide,hb,by decide,by decide,?_⟩
  rw [hb]
  simp only [List.mem_singleton, forall_eq]
  decide

theorem generated_match_event_possible :
    AcceptedHonestTargetMatch hashes.ballot 1 3 false (aliceCoins,rejectedBobCoins)
      (strongHonestBallot hashes.ballot 1 3 true bobCoins) := by
  constructor
  · decide
  · exact ⟨true,some 0,some 0,by decide⟩

/-- The general bound applies to any probabilistic continuation, including
one that is given all honest coins. This is not a secrecy statement. -/
theorem fixture_match_probability_le
    (next : HonestCoins Scalar × HonestCoins Scalar →
      ProbComp (StatementHash Scalar Scalar × Ballot Scalar Scalar 2)) :
    Pr[fun out => AcceptedHonestTargetMatch out.2.1 1 3 false out.1 out.2.2 |
      (do let pair ← drawHonestPair Scalar; let out ← next pair; pure (pair,out))] ≤ 9 / 10 := by
  have hg : Function.Injective (fun r : Scalar => r • (1 : Scalar)) := by
    intro a b h; simpa [smul_eq_mul] using h
  have h := accepted_honest_target_match_probability_le 1 3 hg false next
  norm_num [noncePointBound] at h ⊢
  exact h

private theorem nonzero_supported (r : Scalar) (hr : r ≠ 0) : r ∈ support (sampleNonzero Scalar) := by
  simp only [sampleNonzero,support_map]
  exact ⟨Units.mk0 r hr,by simp,rfl⟩

private theorem triple_supported (r : Scalar) (hr : r ≠ 0) :
    (fun _ : Fin 3 => r) ∈ support (drawTriple Scalar) := by
  simp only [drawTriple,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff]
  refine ⟨r,nonzero_supported r hr,r,nonzero_supported r hr,r,nonzero_supported r hr,?_⟩
  funext i; fin_cases i <;> rfl

private theorem coins_supported (r s : Scalar) (hr : r ≠ 0) (hs : s ≠ 0) :
    (⟨![r,s],fun _ => 4,fun _ => 2,fun _ => 3⟩ : HonestCoins Scalar) ∈
      support (drawHonestCoins Scalar) := by
  simp only [drawHonestCoins,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff]
  refine ⟨_,triple_supported 4 (by decide),_,triple_supported 2 (by decide),
    _,triple_supported 3 (by decide),(r,s),?_,rfl⟩
  simp only [drawNoncePair,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff]
  exact ⟨r,nonzero_supported r hr,s,nonzero_supported s hs,rfl⟩

theorem rejection_fixture_reachable :
    (aliceCoins,rejectedBobCoins) ∈ support (drawHonestPair Scalar) := by
  simp only [drawHonestPair,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff]
  exact ⟨aliceCoins,coins_supported 1 2 (by decide) (by decide),
    rejectedBobCoins,coins_supported 4 2 (by decide) (by decide),rfl⟩

/-- Matching a rejected honest target has positive probability under the
original nonzero sampler, not merely a satisfying unsampled coin assignment. -/
theorem generated_match_event_positive :
    0 < Pr[fun pair => AcceptedHonestTargetMatch hashes.ballot 1 3 false pair
      (strongHonestBallot hashes.ballot 1 3 true bobCoins) | drawHonestPair Scalar] := by
  exact probEvent_pos_iff.mpr ⟨(aliceCoins,rejectedBobCoins),
    rejection_fixture_reachable,generated_match_event_possible⟩

#print axioms fresh_third_ballot_accepted
#print axioms literal_third_ciphertexts
#print axioms cross_kind_copy_rejected
#print axioms rejected_honest_target_can_recur
#print axioms generated_match_event_possible
#print axioms fixture_match_probability_le
#print axioms rejection_fixture_reachable
#print axioms generated_match_event_positive
end ExplainableCrypto.Helios.Computational.BallotProofProvenanceControls
