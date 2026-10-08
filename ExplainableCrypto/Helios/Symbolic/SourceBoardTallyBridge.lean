import ExplainableCrypto.Helios.Symbolic.SourceBoardTallyProgram
import ExplainableCrypto.Helios.Symbolic.SourceNamedElectionStatic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type} {n : Nat}

/-- Rewrite only the saved tally values in a finite template. Its private
send, fresh partial input, and both public output prefixes are retained. -/
theorem boardRegisterFinish_structural (ch : Channels) (tallies : Fin (n+1) → Term V) :
    Extended.Structural
      (.plain (boardRegisterFinish ch (candidateTuple tallies) tallies))
      (.plain (boardRegisterFinish (n := n) ch (candidateTuple tallies)
        (fun j => (candidateTuple tallies).project j.val))) := by
  let p : Agent (Fin (n+2)) := boardRegisterFinish ch (.var 0) (fun j : Fin (n+1) => .var j.succ)
  let σ : Fin (n+2) → Term V := Fin.cases (candidateTuple tallies) tallies
  let τ : Fin (n+2) → Term V := Fin.cases (candidateTuple tallies)
    (fun j => (candidateTuple tallies).project j.val)
  have he (i : Fin (n+2)) : EqE (σ i) (τ i) := by
    refine Fin.cases (.refl _) (fun j => ?_) i
    exact (candidateTuple_project tallies j).symm
  simpa only [p,σ,τ,boardRegisterFinish_subst,Term.subst,Fin.cases_zero,Fin.cases_succ] using
    p.finite_subst_structural σ τ he

/-- Figure 4's direct tally variables and the existing tuple-projection
continuation coincide through actual source rules, not only payload EquivE. -/
theorem boardTallyProgram_normalizes (ch : Channels) (first second : Term V) (others : List (Term V)) :
    Extended.Structural (boardTallyProgram (n := n) ch first second others).compile
      (.plain (boardFinish (n := n) ch first second others)) := by
  apply (boardTallyProgram (n := n) ch first second others).compile_normalizes.trans
  rw [boardTallyProgram_value]
  have h := boardRegisterFinish_structural ch (boardTally (n := n) first second others)
  simpa only [tallyMessage,boardRegisterFinish,boardFinish,publishBody,resultBody,
    shiftTerm,Term.subst_project] using h

/-- The explicit block at the reached tallying stage, alongside the waiting
trustee. No ballot-collection prefix is silently added to the source AST. -/
def computedBoardTallyBody (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) (ch : Channels) : Extended Empty :=
  .par ((boardTallyProgram (n := n) ch (ballot ns 0 (choice swap left right 0).value)
    (ballot ns 1 (choice swap left right 1).value)
    (receivedBallots ns swap left right rs)).compile)
    (.plain (trusteeAgent (n := n) ch (.name ns.secretKey)))

theorem computedBoardTallyBody_normalizes (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (extra : Nat) (ch : Channels) :
    Extended.Structural (computedBoardTallyBody ns swap left right rs ch)
      (.plain (residual ns swap left right extra ch (.sendTally rs))) :=
  (Extended.Structural.parLeft _ (boardTallyProgram_normalizes ch _ _ _)).trans
    (Extended.Structural.plainPar _ _).symm

noncomputable def computedBoardTallyState (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (ch : Channels) : Named (Fin 3) :=
  Named.restrictNames (Named.restrictionNames ch.privateChannels ns.restricted)
    (.embed (.par (Extended.activeFrame (sourceView ns swap left right (.sendTally rs)))
      ((computedBoardTallyBody ns swap left right rs ch).rename Empty.elim)))

theorem computedBoardTallyState_normalizes (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (extra : Nat) (ch : Channels) :
    Named.Structural (computedBoardTallyState ns swap left right rs ch)
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch (.sendTally rs))) := by
  have h := (computedBoardTallyBody_normalizes ns swap left right rs extra ch).rename
    (Empty.elim : Empty → Fin 3) (fun x => x.elim)
  have he : (fun v : Empty => Term.var (Empty.elim v : Fin 3)) = Empty.elim := by
    funext v; exact v.elim
  simpa only [Process.Phase.handles,computedBoardTallyState,Named.restrictedState,sourceState,
    Extended.frameProcess,Extended.rename,Extended.groundAgent,he] using
    (Named.Structural.embed (Extended.Structural.parRight
      (Extended.activeFrame (sourceView ns swap left right (.sendTally rs))) h)).restrictNames
        (Named.restrictionNames ch.privateChannels ns.restricted)

theorem computedBoardTallyState_represents (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (ch : Channels) :
    (computedBoardTallyState ns swap left right rs ch).RepresentsFrame ch.privateChannels
      (sourceView ns swap left right (.sendTally rs)) :=
  (Named.restrictedState_represents (sourceState ns swap left right 0 ch (.sendTally rs))).structural
    (computedBoardTallyState_normalizes ns swap left right rs 0 ch).symm

theorem computedBoardTallyState_wellFormed (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (ch : Channels) :
    (computedBoardTallyState ns swap left right rs ch).WellFormed :=
  (computedBoardTallyState_represents ns swap left right rs ch).wellFormed

theorem computedBoardTallyState_staticEq {ns : Names n} (hf : ns.Fresh)
    {left right : CandidateSubstitution n Empty} {rs : List (Recipe 3)} {extra : Nat}
    (hr : Process.Reachable ns false left right extra (.sendTally rs)) (ch : Channels) :
    Named.StaticEq (computedBoardTallyState ns false left right rs ch)
      (computedBoardTallyState ns true left right rs ch) :=
  Named.reachable_structural_source_staticEq hf hr ch
    (computedBoardTallyState_normalizes ns false left right rs extra ch).symm
    (computedBoardTallyState_normalizes ns true left right rs extra ch).symm

/-- Exact target and label interfaces survive the expanded tally block,
including actions through arbitrary structural representatives. -/
theorem computedBoardTallyState_reduction_iff (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (extra : Nat)
    (ch : Channels) (b : Named (Fin 3)) :
    Named.Reduction (computedBoardTallyState ns swap left right rs ch) b ↔
      Named.Reduction (Named.restrictedState ch.privateChannels
        (sourceState ns swap left right extra ch (.sendTally rs))) b := by
  have h := computedBoardTallyState_normalizes ns swap left right rs extra ch
  exact ⟨fun ha => .congr h.symm ha (.refl _),fun ha => .congr h ha (.refl _)⟩

theorem computedBoardTallyState_free_iff (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (extra : Nat)
    (ch : Channels) (l : Extended.FreeLabel (Fin 3)) (b : Named (Fin 3)) :
    Named.FreeStep (computedBoardTallyState ns swap left right rs ch) l b ↔
      Named.FreeStep (Named.restrictedState ch.privateChannels
        (sourceState ns swap left right extra ch (.sendTally rs))) l b := by
  have h := computedBoardTallyState_normalizes ns swap left right rs extra ch
  exact ⟨fun ha => .congr h.symm ha (.refl _),fun ha => .congr h ha (.refl _)⟩

theorem computedBoardTallyState_bound_iff (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (extra : Nat)
    (ch : Channels) (channel : Nat) (b : Named (Option (Fin 3))) :
    Named.BoundOutput (computedBoardTallyState ns swap left right rs ch) channel b ↔
      Named.BoundOutput (Named.restrictedState ch.privateChannels
        (sourceState ns swap left right extra ch (.sendTally rs))) channel b := by
  have h := computedBoardTallyState_normalizes ns swap left right rs extra ch
  exact ⟨fun ha => .congr h.symm ha (.refl _),fun ha => .congr h ha (.refl _)⟩

/-- A real private communication is enabled; the expansion does not merely
produce a well-formed, statically indistinguishable but stuck process. -/
theorem computedBoardTallyState_sends (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (extra : Nat) (ch : Channels) :
    Named.Reduction (computedBoardTallyState ns swap left right rs ch)
      (Named.restrictedState ch.privateChannels
        (sourceState ns swap left right extra ch (.trusteeReply rs))) := by
  apply (computedBoardTallyState_reduction_iff ns swap left right rs extra ch _).mpr
  apply Named.restricted_tau_derivable
  exact ScopedStep.tau _ (residual_sendTally ns swap left right extra ch rs)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
