import ExplainableCrypto.Helios.Symbolic.ConstructedCheckTransport
import ExplainableCrypto.Helios.Symbolic.StaticAcceptance

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- A minimum equivalent of an honest combination agrees already under raw
E0. Its value binding therefore transfers through every frame substitution. -/
theorem minimum_honest_combination_baseEq (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns swap left right).value r)
    (a : Combination (HonestIndex n))
    (he : EqE ((frame ns swap left right).eval r) ((frame ns swap left right).eval (combinationRecipe a))) :
    BaseEq r (combinationRecipe a) := by
  obtain ⟨b,rfl,hb⟩ := minimum_honest_combination_origin ns hf swap left right r hr a he
  exact Combination.evaluate_baseEq_of_indices .mul trivial _ hb

/-- The exact nonempty candidate fold for one voter, with every index once. -/
def voterCombination (i : Fin 2) : Combination (HonestIndex n) :=
  (List.finRange n).foldl (fun acc j => .mul acc (.leaf (i,j.succ))) (.leaf (i,0))

theorem voterCombination_evaluate {V : Type} (i : Fin 2) (f : Binary) (values : HonestIndex n → Term V) :
    (voterCombination i).evaluate f values = foldCandidates f (fun j => values (i,j)) := by
  have fold (xs : List (Fin n)) (acc : Combination (HonestIndex n)) :
      (xs.foldl (fun acc j => .mul acc (.leaf (i,j.succ))) acc).evaluate f values =
        xs.foldl (fun acc j => .binary f acc (values (i,j.succ))) (acc.evaluate f values) := by
    induction xs generalizing acc with
    | nil => rfl
    | cons j xs ih => exact ih (.mul acc (.leaf (i,j.succ)))
  exact fold _ _

theorem voterCombination_recipe (i : Fin 2) :
    combinationRecipe (voterCombination (n := n) i) = aggregateCiphertext n (.var i.succ) := by
  rw [combinationRecipe,voterCombination_evaluate]
  rfl

theorem voterCombination_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) :
    EqE ((frame ns swap left right).eval (combinationRecipe (voterCombination (n := n) i)))
      (foldCandidates .mul (ciphertext ns i (choice swap left right i).value)) := by
  rw [voterCombination_recipe,Frame.eval,aggregateCiphertext_subst]
  simpa only [Term.subst,frame_voter_handle] using
    ballot_aggregate_ciphertext ns i (choice swap left right i).value

/-- Honest binding transfer uses the ciphertext's minimum origin, so it does
not require a possibly oversized aggregate-recipe comparison. The public-key
test alone uses the strictly smaller observation premise. -/
theorem honest_check_success_transfer (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (a b c : Recipe 3)
    (ha : a.Public ns.restricted)
    (hb : MinimalRecipe ns.restricted (frame ns swap left right).value b)
    (t : Combination (HonestIndex n))
    (hp : ∃ r m, EqE ((frame ns swap left right).eval c)
      (.spk (publicKey ns) r m ((frame ns swap left right).eval (combinationRecipe t))))
    (hvalid : EqE (.ternary .checkspk (publicKey ns)
      ((frame ns swap' left right).eval (combinationRecipe t)) ((frame ns swap' left right).eval c)) (.const .ok))
    (hobs : Frame.ObservationsBelow (frame ns swap left right) (frame ns swap' left right)
      (Term.ternary .checkspk a b c).nodeCount)
    (he : EqE ((frame ns swap left right).eval (.ternary .checkspk a b c)) (.const .ok)) :
    EqE ((frame ns swap' left right).eval (.ternary .checkspk a b c)) (.const .ok) := by
  obtain ⟨r,m,hp⟩ := hp
  obtain ⟨nr,bit,_,_,hproof⟩ := (EqE.check_ok_iff_components _ _ _).mp he
  have hs := (EqE.spk_iff _ _ _ _ _ _ _ _).mp (hp.symm.trans hproof)
  have hraw := minimum_honest_combination_baseEq ns hf swap left right b hb t hs.2.2.2.symm
  have hk : EqE ((frame ns swap' left right).eval a) (publicKey ns) := by
    apply (hobs a (.var 0) ha trivial ?_).mp hs.1.symm
    have hcpos := c.nodeCount_pos
    simp only [Term.nodeCount]
    omega
  exact (EqE.ternary .checkspk hk (hraw.sound.subst _) (.refl _)).trans hvalid

end ExplainableCrypto.Helios.Symbolic.Historical.General
