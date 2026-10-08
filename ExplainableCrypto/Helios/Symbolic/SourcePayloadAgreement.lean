import ExplainableCrypto.Helios.Symbolic.SourcePayloadSyntax

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W : Type} {n : Nat}

/-- Input respects the source's E-rewrite rule for the body and message. -/
theorem bindInput_congr {body body' : Term (Option V)} {message message' : Term V}
    (hb : EqE body body') (hm : EqE message message') :
    EqE (bindInput body message) (bindInput body' message') := by
  apply (hb.subst (inputSubst message)).trans
  exact body'.subst_congr _ _ (fun v => by cases v; exact hm; exact .refl _)

theorem boardTally_subst (first second : Term V) (others : List (Term V))
    (j : Fin (n+1)) (σ : V → Term W) :
    (boardTally first second others j).subst σ =
      boardTally (first.subst σ) (second.subst σ) (others.map (Term.subst σ)) j := by
  have fold (xs : List (Term V)) (acc : Term V) :
      (xs.foldl (fun a b => .binary .mul a (b.project j.val)) acc).subst σ =
      (xs.map (Term.subst σ)).foldl (fun a b => .binary .mul a (b.project j.val)) (acc.subst σ) := by
    induction xs generalizing acc with
    | nil => rfl
    | cons x xs ih => simp only [List.foldl_cons,List.map_cons,ih,Term.subst,Term.subst_project]
  simpa only [boardTally,Term.subst,Term.subst_project] using fold others (.binary .mul (first.project j.val) (second.project j.val))

theorem tallyMessage_subst (first second : Term V) (others : List (Term V)) (σ : V → Term W) :
    (tallyMessage (n := n) first second others).subst σ =
      tallyMessage (n := n) (first.subst σ) (second.subst σ) (others.map (Term.subst σ)) := by
  simp only [tallyMessage,candidateTuple_subst,boardTally_subst]

/-- The fresh tally input really substitutes into each trustee projection. -/
theorem trusteeMessage_expand (secret tallies : Term V) :
    trusteeMessage (n := n) secret tallies =
      candidateTuple (n := n) (fun j => .binary .partialDecrypt secret (tallies.project j.val)) := by
  simp only [trusteeMessage,bindInput,trusteeBody,candidateTuple_subst,Term.subst,
    Term.subst_project,Term.subst_subst,inputSubst,Term.subst_var]

theorem resultMessage_expand (tallies partials : Term V) :
    resultMessage (n := n) tallies partials =
      candidateTuple (n := n) (fun j => .binary .dec (partials.project j.val) (tallies.project j.val)) := by
  simp only [resultMessage,bindInput,resultBody,candidateTuple_subst,Term.subst,
    Term.subst_project,Term.subst_subst,inputSubst,Term.subst_var]

/-- The private trustee reply agrees componentwise for any nonempty tally
vector. No acceptance, honest encryption shape, or decryption success is used. -/
theorem trusteeMessage_tuple (secret : Term V) (tallies : Fin (n+1) → Term V) :
    EqE (trusteeMessage (n := n) secret (candidateTuple tallies))
      (candidateTuple (fun j => .binary .partialDecrypt secret (tallies j))) := by
  rw [trusteeMessage_expand]
  exact EqE.candidateTuple _ _ (fun j => .binary .partialDecrypt (.refl _) (candidateTuple_project tallies j))

/-- The return input preserves complete per-candidate ciphertext binding. -/
theorem resultMessage_tuples (tallies partials : Fin (n+1) → Term V) :
    EqE (resultMessage (n := n) (candidateTuple tallies) (candidateTuple partials))
      (candidateTuple (fun j => .binary .dec (partials j) (tallies j))) := by
  rw [resultMessage_expand]
  exact EqE.candidateTuple _ _ (fun j => .binary .dec
    (candidateTuple_project partials j) (candidateTuple_project tallies j))

theorem trusteeMessage_congr {secret secret' tallies tallies' : Term V}
    (hk : EqE secret secret') (ht : EqE tallies tallies') :
    EqE (trusteeMessage (n := n) secret tallies) (trusteeMessage (n := n) secret' tallies') := by
  rw [trusteeMessage_expand,trusteeMessage_expand]
  exact EqE.candidateTuple _ _ (fun j => .binary .partialDecrypt hk (.unary .fst (ht.drop j.val)))

theorem resultMessage_congr {tallies tallies' partials partials' : Term V}
    (ht : EqE tallies tallies') (hp : EqE partials partials') :
    EqE (resultMessage (n := n) tallies partials) (resultMessage (n := n) tallies' partials') := by
  rw [resultMessage_expand,resultMessage_expand]
  exact EqE.candidateTuple _ _ (fun j => .binary .dec (.unary .fst (hp.drop j.val)) (.unary .fst (ht.drop j.val)))

/-- Literal source board expressions equal the already checked tally recipe
after evaluating every received ballot. There is no omitted final input. -/
theorem sourceTallies_eq (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) :
    sourceTallies ns swap left right rs = candidateTuple (tallyCiphertext ns swap left right rs) := by
  unfold sourceTallies tallyMessage
  congr 1
  funext j
  have h := boardTally_subst (.var (1 : Fin 3)) (.var 2) rs j (frame ns swap left right).value
  have h₀ : (frame ns swap left right).value 1 = ballot ns 0 (choice swap left right 0).value :=
    frame_voter_handle ns swap left right 0
  have h₁ : (frame ns swap left right).value 2 = ballot ns 1 (choice swap left right 1).value :=
    frame_voter_handle ns swap left right 1
  unfold tallyCiphertext Frame.eval
  simpa only [Term.subst,h₀,h₁,boardTally,tallyRecipe] using h.symm

theorem sourcePartials_eqE (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) :
    EqE (sourcePartials ns swap left right rs) (candidateTuple (tallyPartial ns swap left right rs)) := by
  unfold sourcePartials
  rw [sourceTallies_eq]
  exact trusteeMessage_tuple _ _

theorem sourceResults_eqE (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) :
    EqE (sourceResults ns swap left right rs) (candidateTuple (tallyResult ns swap left right rs)) := by
  unfold sourceResults
  rw [sourceTallies_eq]
  exact (resultMessage_congr (.refl _) (sourcePartials_eqE ns swap left right rs)).trans
    (resultMessage_tuples _ _)

/-- Source outputs and stage outputs agree at every retained/added handle. -/
theorem source_partial_pointwise (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) (i : Fin 4) :
    EqE ((sourcePartialFrame ns swap left right rs).value i) ((partialFrame ns swap left right rs).value i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [sourcePartialFrame,partialFrame,Frame.extend_last] using sourcePartials_eqE ns swap left right rs
  · simp only [sourcePartialFrame,partialFrame,Frame.extend_old]
    exact .refl _

theorem source_final_pointwise (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) (i : Fin 5) :
    EqE ((sourceFinalFrame ns swap left right rs).value i) ((finalFrame ns swap left right rs).value i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [sourceFinalFrame,finalFrame,Frame.extend_last] using sourceResults_eqE ns swap left right rs
  · simpa only [sourceFinalFrame,finalFrame,Frame.extend_old] using source_partial_pointwise ns swap left right rs j

/-- This compares actual source expression outputs, still prior to any process
operational-correspondence or bisimilarity claim. -/
theorem source_final_staticEq (ns : Names n) (hf : ns.Fresh) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs) :
    Frame.StaticEq (sourceFinalFrame ns false left right rs) (sourceFinalFrame ns true left right rs) :=
  (Frame.staticEq_of_pointwise (source_final_pointwise ns false left right rs)).trans
    ((accepted_final_staticEq ns hf left right rs hp ha).trans
      (Frame.staticEq_of_pointwise (source_final_pointwise ns true left right rs)).symm)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
