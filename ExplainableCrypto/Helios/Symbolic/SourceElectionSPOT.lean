import ExplainableCrypto.Helios.Symbolic.SourceElectionReduction
import ExplainableCrypto.Helios.Symbolic.SourcePayloadSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceElectionSPOT
open Historical General Source
abbrev ch := Channels.canonical
abbrev names := SharedTallySPOT.names
abbrev key := publicKey names
abbrev world := SharedTallySPOT.world
abbrev honestFirst (swap : Bool) := (world swap).eval (.var 1)
abbrev honestSecond (swap : Bool) := (world swap).eval (.var 2)
abbrev incoming (swap : Bool) := (world swap).eval SharedTallySPOT.first

private def headTag {V : Type} : Agent V → Nat × Nat
  | .nil => (0,0)
  | .par _ _ => (1,0)
  | .output c _ _ => (2,c)
  | .input c _ => (3,c)
  | .branch _ _ _ => (4,0)

/-- The literal allocation keeps all public voter channels apart from the
broadcast and trustee channels; distinctness alone is not restriction. -/
theorem distinct_static_channels :
    ch.broadcast ≠ ch.trustee ∧
    (∀ i, ch.voter i ≠ ch.broadcast ∧ ch.voter i ≠ ch.trustee) ∧
    Function.Injective ch.voter := by
  refine ⟨by decide,?_,?_⟩
  · intro i
    change i+2 ≠ 0 ∧ i+2 ≠ 1
    omega
  · intro i j h
    change i+2=j+2 at h
    omega

/-- The source board begins by receiving the first authenticated ballot. -/
theorem first_honest_input_first (extra : Nat) :
    headTag (boardStart 0 extra ch key) = (3,2) := rfl

/-- The second honest ballot is relayed before any further ballot is read. -/
theorem second_honest_relay (extra : Nat) (first : Ground) :
    boardSecond 0 extra ch key first = .input 3 (.output 0 (.var none)
      (collectBallots 0 ch extra (shiftTerm key) (shiftTerm first) (.var none) [])) := rfl

/-- With no remaining voters the source immediately sends the tally privately. -/
theorem no_extra_enters_private_tally (swap : Bool) :
    headTag (collectBallots 0 ch 0 key (honestFirst swap) (honestSecond swap) []) = (2,1) := rfl

/-- A remaining voter forces the input prefix, at the next channel after the
already accepted inputs. A premature private tally send has a different head. -/
theorem pending_voter_blocks_tally (swap : Bool) (remaining : Nat) (others : List Ground) :
    headTag (collectBallots 0 ch (remaining+1) key (honestFirst swap) (honestSecond swap) others) =
      (3,others.length+4) ∧
    headTag (collectBallots 0 ch (remaining+1) key (honestFirst swap) (honestSecond swap) others) ≠ (2,1) := by
  refine ⟨?_,?_⟩
  · simp only [collectBallots,headTag,ch,Channels.canonical,Nat.add_assoc]
  · intro h
    have hh := congrArg Prod.fst h
    cases hh

private theorem incoming_accepted (swap : Bool) :
    Accepted 0 key [honestFirst swap,honestSecond swap] (incoming swap) := by
  have h := (SharedTallySPOT.fresh_sequence_accepted swap).1
  change Accepted 0 key [honestFirst swap,honestSecond swap] (incoming swap) at h
  exact h

/-- A real fresh ballot takes the last successful check into a tally containing
that ballot, rather than dropping the final voter. -/
theorem fresh_last_input_enters_tally (swap : Bool) :
    Agent.CoreStep
      (.branch (electionGuard 0 key [honestFirst swap,honestSecond swap] (incoming swap))
        (collectBallots 0 ch 0 key (honestFirst swap) (honestSecond swap) [incoming swap]) .nil)
      (boardFinish (n := 0) ch (honestFirst swap) (honestSecond swap) [incoming swap]) :=
  collection_accept 0 0 ch key (honestFirst swap) (honestSecond swap) (incoming swap) [] (incoming_accepted swap)

/-- Replay reaches null in the actual finite guard. Null has no further core
reductions; no later-voter continuation survives rejection. -/
theorem replay_stops_collection (swap : Bool) (remaining : Nat) :
    Agent.CoreStep
      (.branch (electionGuard 0 key [honestFirst swap,honestSecond swap] (honestFirst swap))
        (collectBallots 0 ch remaining key (honestFirst swap) (honestSecond swap) [honestFirst swap]) .nil) .nil ∧
    ∀ p, ¬ Agent.CoreStep .nil p := by
  refine ⟨collection_reject 0 remaining ch key (honestFirst swap) (honestSecond swap) (honestFirst swap) [] ?_,
    Agent.nil_no_coreStep⟩
  exact accepted_excludes_replay 0 key (honestFirst swap) _ (by simp)

/-- Dropping the accumulated board is a detected guard mutant: the valid ballot
passes on an empty board but fails when it is already present. -/
theorem omitted_board_mutant_detected (k nonce : Ground) :
    (electionGuard 0 k [] (oneCandidateBallot k nonce)).Holds Empty.elim ∧
    ¬ (electionGuard 0 k [oneCandidateBallot k nonce] (oneCandidateBallot k nonce)).Holds Empty.elim := by
  refine ⟨(electionGuard_ground _ _ _ _).mpr (oneCandidate_corrected_accepts k nonce),?_⟩
  intro h
  exact accepted_excludes_replay 0 k (oneCandidateBallot k nonce) _ (by simp)
    ((electionGuard_ground _ _ _ _).mp h)

/-- Reuse across different candidate positions is rejected, even if a mutant
only comparing equal positions might miss it. No proof-validity premise is used. -/
theorem cross_candidate_reuse_rejected (k : Ground) :
    let earlier : Ground := .binary .pair (.name 40) (.binary .pair (.name 41) (.const .bottom))
    let later : Ground := .binary .pair (.name 41) (.binary .pair (.name 40) (.const .bottom))
    ¬ (electionGuard 1 k [earlier] later).Holds Empty.elim := by
  dsimp only
  intro h
  have ha := (electionGuard_ground _ _ _ _).mp h
  apply ha.2.2 (.binary .pair (.name 40) (.binary .pair (.name 41) (.const .bottom)))
    (by simp) (0 : Fin 2) (1 : Fin 2)
  have h₀ : EqE ((Term.binary .pair (.name 40) (.binary .pair (.name 41) (.const .bottom)) : Ground).project 0) (.name 40) :=
    .equation (.fst _ _)
  have h₁ : EqE ((Term.binary .pair (.name 41) (.binary .pair (.name 40) (.const .bottom)) : Ground).project 1) (.name 40) :=
    (EqE.unary .fst (.equation (.snd _ _))).trans (.equation (.fst _ _))
  exact h₀.trans h₁.symm

/-- Binding the first honest variable under the second input keeps their order
in the final tally, rather than capturing the later input. -/
theorem honest_input_binding_order :
    (Agent.output 0 (.var none) (boardSecond 0 0 ch (shiftTerm (.var (7 : Nat))) (.var none))).bind (.name 40) =
      .output 0 (.name 40) (.input 3 (.output 0 (.var none)
        (boardFinish (n := 0) ch (.name 40) (.var none) []))) := by
  simpa only [boardSecond,collectBallots,shiftTerm,Term.subst,ch,Channels.canonical] using
    boardFirst_bind 0 0 ch (.var (7 : Nat)) (.name 40)

/-- The partial tuple is the first public output and the candidate results the
second. The source expression's tuple projections remain present before E. -/
theorem private_reply_output_order (tallies partials : Ground) :
    (publishBody (n := 1) ch tallies).bind partials =
      .output 0 partials (.output 0 (resultMessage (n := 1) tallies partials) .nil) := rfl

/-- A real source trustee reply and its board input use the same complete
multi-candidate payload already checked against the published frames. -/
theorem actual_private_exchange (swap : Bool) :
    let tallies := sourceTallies LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right []
    let partials := sourcePartials LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right []
    Agent.CoreStep
      (.par (.output 1 partials .nil) (.input 1 (publishBody (n := 1) ch tallies)))
      (.par .nil (.output 0 partials
        (.output 0 (sourceResults LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right []) .nil))) ∧
    EqE ((sourceResults LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right []).project 0) (.const .zero) ∧
    EqE ((sourceResults LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right []).project 1) (.const .one) := by
  exact ⟨board_reply_communication ch _ _,SourcePayloadSPOT.actual_candidate_results swap⟩
end ExplainableCrypto.Helios.Symbolic.SourceElectionSPOT
