import ExplainableCrypto.Helios.Symbolic.HistoricalProcessMatching
import ExplainableCrypto.Helios.Symbolic.HistoricalProcessExperiments
import ExplainableCrypto.Helios.Symbolic.TrusteeFreeSPOT

namespace ExplainableCrypto.Helios.Symbolic.HistoricalProcessSPOT
open Historical General Process
abbrev names := SharedTallySPOT.names
abbrev left := SharedTallySPOT.left
abbrev right := SharedTallySPOT.right
abbrev first := SharedTallySPOT.first
abbrev second := SharedTallySPOT.second

private theorem honest_prefix (swap : Bool) (extra : Nat) :
    Reachable names swap left right extra (afterAccepted extra []) :=
  (((Relation.ReflTransGen.refl.tail ⟨.tau,Step.receiveFirst⟩).tail ⟨.output 1,Step.publishFirst⟩).tail
    ⟨.tau,Step.receiveSecond⟩).tail ⟨.output 2,Step.publishSecond⟩

private theorem suffix (swap : Bool) (extra : Nat) (rs : List (Recipe 3))
    (h : Reachable names swap left right extra (.sendTally rs)) :
    Reachable names swap left right extra (.done rs) :=
  (((h.tail ⟨.tau,Step.sendTally⟩).tail ⟨.tau,Step.receivePartial⟩).tail
    ⟨.output 3,Step.publishPartial⟩).tail ⟨.output 4,Step.publishResult⟩

private theorem ballot_public (nonce : Nat) (bit : Constant) (hn : nonce ∉ names.restricted) :
    (ElectionTallyExperiments.publicBallot nonce bit).Public names.restricted := by
  apply constructorBallot_public
  · trivial
  · intro _; exact hn
  · intro _; trivial
  · intro _; exact ⟨trivial,hn,trivial,trivial,hn,trivial⟩

/-- The two-honest-voter election actually reaches both output publications. -/
theorem zero_extra_completes (swap : Bool) : Reachable names swap left right 0 (.done []) := by
  apply suffix
  simpa only [afterAccepted,List.length_nil,lt_self_iff_false,if_false] using honest_prefix swap 0

/-- A concrete sequence of two public ballots is consumed on channels 2 and 3,
passes both checks, and reaches a final state with its whole accepted history. -/
theorem two_extra_complete (swap : Bool) : Reachable names swap left right 2 (.done [first,second]) := by
  have p : Reachable names swap left right 2 (.input []) := by simpa [afterAccepted] using honest_prefix swap 2
  have a : accepts names swap left right [] first := by
    have ha := (SharedTallySPOT.fresh_sequence_accepted swap).1
    have hk : (SharedTallySPOT.world swap).eval (.var 0) = publicKey names := rfl
    rw [hk] at ha
    exact ha
  have b : accepts names swap left right [first] second := (SharedTallySPOT.fresh_sequence_accepted swap).2.1
  have q := p.tail ⟨.input 2 first,Step.input (by decide) (ballot_public 40 .one (by decide))⟩
  have r : Reachable names swap left right 2 (.input [first]) := by
    simpa [Reachable,afterAccepted] using q.tail ⟨.tau,Step.accept a⟩
  have s := r.tail ⟨.input 3 second,Step.input (by decide) (ballot_public 41 .zero (by decide))⟩
  apply suffix
  simpa [Reachable,afterAccepted] using s.tail ⟨.tau,Step.accept b⟩

/-- A real public replay is received before failing the check. Rejection is
reachable and has no outgoing internal or visible transition. -/
theorem replay_stops (swap : Bool) :
    Reachable names swap left right 1 (.rejected []) ∧
    ∀ a q, ¬ Step names swap left right 1 (.rejected []) a q := by
  have p : Reachable names swap left right 1 (.input []) := by simpa [afterAccepted] using honest_prefix swap 1
  have q := p.tail ⟨.input 2 (.var 1),Step.input (by decide) (by trivial)⟩
  have hn : ¬ accepts names swap left right [] (.var 1) := by
    intro h
    apply SharedTallySPOT.honest_replay_rejected swap
    exact ⟨h,True.intro⟩
  exact ⟨q.tail ⟨.tau,Step.reject hn⟩,rejected_no_step names swap left right 1 []⟩

/-- Final publication cannot omit an eligible input. This follows from actual
reachability, not an extra successful-history premise on the theorem. -/
theorem missing_voter_cannot_finish (swap : Bool) :
    ¬ Reachable names swap left right 1 (.done []) := by
  intro h
  have hc := (reachable_done_history h).1
  cases hc

/-- The public output of partials must precede the fresh result handle. -/
theorem output_order (swap : Bool) :
    Step names swap left right 0 (.partialReady []) (.output 3) (.resultReady []) ∧
    Step names swap left right 0 (.resultReady []) (.output 4) (.done []) ∧
    ¬ Step names swap left right 0 (.partialReady []) (.output 4) (.done []) := by
  refine ⟨.publishPartial,.publishResult,?_⟩
  intro h
  cases h

/-- The second attacker input belongs to the next eligible voter, not a repeat
of the previous channel. -/
theorem input_order (swap : Bool) :
    Step names swap left right 2 (.input [first]) (.input 3 second) (.check [first] second) ∧
    ¬ Step names swap left right 2 (.input [first]) (.input 2 second) (.check [first] second) := by
  refine ⟨.input (by decide) (ballot_public 41 .zero (by decide)),?_⟩
  intro h
  cases h

/-- All received recipes obey the policy even though malformed public ballots
may be received and rejected. A literal secret-key input cannot occur. -/
theorem restricted_input_forbidden (swap : Bool) :
    ¬ Step names swap left right 1 (.input []) (.input 2 (.name names.secretKey))
      (.check [] (.name names.secretKey)) := by
  intro h
  have hp := h.input_scope.2.1
  exact hp (by simp [Names.restricted])

/-- The public domain grows only when a message is output; private receives
neither expose the second honest ballot nor trustee messages early. -/
theorem intermediate_domains :
    Phase.start.handles=1 ∧ Phase.firstReceived.handles=1 ∧
    Phase.firstPublished.handles=2 ∧ Phase.secondReceived.handles=2 ∧
    (Phase.partialReady []).handles=3 ∧ (Phase.resultReady []).handles=4 ∧ (Phase.done []).handles=5 := by
  decide

/-- The matching theorem is inhabited by unequal candidates and a nonempty
completed election, with tally two and distinct public names retained. -/
theorem completed_observations_noncollapsed :
    Frame.StaticEq (view names false left right (.done [first,second]))
      (view names true left right (.done [first,second])) ∧
    EqE ((view names true left right (.done [first,second])).eval ((Term.var (4 : Fin 5)).project 0))
      (addNumeral 2) ∧
    ¬ EqE ((view names true left right (.done [first,second])).eval (.name 40))
      ((view names true left right (.done [first,second])).eval (.name 41)) := by
  refine ⟨reachable_view_staticEq NumericReflectionSPOT.fixture_names_fresh (two_extra_complete false),?_,?_⟩
  · exact (finalFrame_result_project names true left right [first,second] 0).trans
      (SharedTallySPOT.fresh_sequence_tally_two.1 true)
  · intro h
    have hn := (EqE.name_iff 40 41).mp h
    omega

/-- Rejection preserves all existing public equality observations. The
reachable rejected state is paired with successful executions above. -/
theorem rejected_stage_observations :
    Frame.StaticEq (view names false left right (.rejected [])) (view names true left right (.rejected [])) :=
  reachable_stage_matching NumericReflectionSPOT.fixture_names_fresh (replay_stops false).1 |>.1

end ExplainableCrypto.Helios.Symbolic.HistoricalProcessSPOT
