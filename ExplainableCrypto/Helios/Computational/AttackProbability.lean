import ExplainableCrypto.Helios.Computational.AttackGame

/-! Probabilistic success of the public proof-reuse attack. The failure bound
comes from honest nonce sampling; the game does not assume freshness or remove
rejected executions. This is an attack theorem, not repaired-protocol secrecy. -/

namespace ExplainableCrypto.Helios.Computational

open OracleComp
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

theorem attackWorld_error_le (hashes : CryptoHashes F G) (g : G)
    (hg : Function.Injective (fun r : F => r • g)) (vote : Bool) :
    Pr[fun view => attackDistinguisher view ≠ vote | attackWorld hashes g vote] ≤
      6 * noncePointBound F := by
  unfold attackWorld
  apply probEvent_bind_le_of_forall_le
  intro secret _
  apply probEvent_bind_le_of_forall_le
  intro keyNonce _
  apply probEvent_bind_le_of_forall_le
  intro decryptionNonces _
  apply (probEvent_bind_pure_comp (drawHonestPair F)
    (fun pair => executeAttack hashes g secret keyNonce ![decryptionNonces.1, decryptionNonces.2]
      vote pair.1 pair.2)
    (fun view => attackDistinguisher view ≠ vote)).trans_le
  apply le_trans ?_ (drawHonestPair_collision_le (F := F))
  apply probEvent_mono
  intro pair hpair hwrong hc
  obtain ⟨ha, hb⟩ := drawHonestPair_support hpair
  exact hwrong (attackDistinguisher_on_good hashes g hg secret keyNonce _ vote pair.1 pair.2
    (drawHonestCoins_nonzero ha) (drawHonestCoins_nonzero hb) hc)

theorem attackWorld_noFailure (hashes : CryptoHashes F G) (g : G) (vote : Bool) :
    Pr[⊥ | attackWorld hashes g vote] = 0 := by
  simp [attackWorld, drawHonestPair, drawHonestCoins, drawTriple, drawNoncePair, sampleNonzero]

noncomputable def attackGuessingGame (hashes : CryptoHashes F G) (g : G) : ProbComp Bool := do
  let vote ← uniformSample Bool
  let view ← attackWorld hashes g vote
  pure (decide (attackDistinguisher view = vote))

theorem attackGuessingGame_error_le (hashes : CryptoHashes F G) (g : G)
    (hg : Function.Injective (fun r : F => r • g)) :
    Pr[= false | attackGuessingGame hashes g] ≤ 6 * noncePointBound F := by
  rw [← probEvent_eq_eq_probOutput]
  unfold attackGuessingGame
  apply probEvent_bind_le_of_forall_le
  intro vote _
  apply (probEvent_bind_pure_comp (attackWorld hashes g vote)
    (fun view => decide (attackDistinguisher view = vote)) (fun success => success = false)).trans_le
  simpa only [Function.comp_def, decide_eq_false_iff_not] using attackWorld_error_le hashes g hg vote

theorem attackGuessingGame_noFailure (hashes : CryptoHashes F G) (g : G) :
    Pr[⊥ | attackGuessingGame hashes g] = 0 := by
  simp [attackGuessingGame, attackWorld, drawHonestPair, drawHonestCoins, drawTriple,
    drawNoncePair, sampleNonzero]

/-- Actual guessing-game success, including every collision/rejection run.
For large scalar fields this approaches one. No cryptographic hardness premise
or caller-supplied freshness/correspondence assumption appears. -/
theorem proofReuse_attack_success (hashes : CryptoHashes F G) (g : G)
    (hg : Function.Injective (fun r : F => r • g)) :
    1 - 6 * noncePointBound F ≤ Pr[= true | attackGuessingGame hashes g] := by
  have htotal := probEvent_compl (attackGuessingGame hashes g) (fun success => success = true)
  have hfalse : (fun success : Bool => ¬ success = true) = (fun success => success = false) := by
    funext success
    cases success <;> simp
  rw [hfalse, attackGuessingGame_noFailure] at htotal
  simp only [probEvent_eq_eq_probOutput, tsub_zero] at htotal
  apply tsub_le_iff_right.mpr
  calc
    (1 : ENNReal) = Pr[= true | attackGuessingGame hashes g] +
        Pr[= false | attackGuessingGame hashes g] := htotal.symm
    _ ≤ Pr[= true | attackGuessingGame hashes g] + 6 * noncePointBound F :=
      add_le_add le_rfl (attackGuessingGame_error_le hashes g hg)

#print axioms attackWorld_error_le
#print axioms attackWorld_noFailure
#print axioms attackGuessingGame_error_le
#print axioms attackGuessingGame_noFailure
#print axioms proofReuse_attack_success

end ExplainableCrypto.Helios.Computational
