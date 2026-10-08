import ExplainableCrypto.Helios.Symbolic.SourceGuardedBoardActions

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- The whole finite ground election with the guarded board compiled in place.
Voter computation/scoping is covered separately by the open-election bridge. -/
def guardedElectionBody (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) : Agent Empty :=
  .par (.output (ch.voter 0) (ballot ns 0 (choice swap left right 0).value) .nil)
    (.par (.output (ch.voter 1) (ballot ns 1 (choice swap left right 1).value) .nil)
      (.par (guardedBoardStart n extra ch (publicKey ns)).inline
        (trusteeAgent (n := n) ch (.name ns.secretKey))))

theorem guardedElectionBody_equivE (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) :
    Agent.EquivE (guardedElectionBody ns swap left right extra ch)
      (electionBody ns swap left right extra ch) :=
  .par (.refl _) (.par (.refl _) (.par (guardedBoardStart_inline_equivE n extra ch _) (.refl _)))

/-- One-step matching at the evaluated plain-process layer. The successor is
related by EvalEq, not asserted equal to an arbitrary Named source successor. -/
theorem guardedElectionBody_tau (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    {p : Agent Empty} (h : Agent.Tau (guardedElectionBody ns swap left right extra ch) p) :
    ∃ q, Agent.Tau (electionBody ns swap left right extra ch) q ∧ Agent.EvalEq p q :=
  (Agent.EvalEq.of_equivE (guardedElectionBody_equivE ns swap left right extra ch)).tau_transport h

theorem guardedElectionBody_tau_reverse (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    {p : Agent Empty} (h : Agent.Tau (electionBody ns swap left right extra ch) p) :
    ∃ q, Agent.Tau (guardedElectionBody ns swap left right extra ch) q ∧ Agent.EvalEq p q :=
  (Agent.EvalEq.of_equivE (guardedElectionBody_equivE ns swap left right extra ch).symm).tau_transport h

theorem guardedElectionBody_visible (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    {p : Agent Empty} {l : Agent.PayloadEvent}
    (h : Agent.Visible (guardedElectionBody ns swap left right extra ch) l p) :
    ∃ l' q, Agent.Visible (electionBody ns swap left right extra ch) l' q ∧
      Agent.PayloadEvent.EquivE l l' ∧ Agent.EvalEq p q :=
  (Agent.EvalEq.of_equivE (guardedElectionBody_equivE ns swap left right extra ch)).visible_transport h

theorem guardedElectionBody_visible_reverse (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    {p : Agent Empty} {l : Agent.PayloadEvent}
    (h : Agent.Visible (electionBody ns swap left right extra ch) l p) :
    ∃ l' q, Agent.Visible (guardedElectionBody ns swap left right extra ch) l' q ∧
      Agent.PayloadEvent.EquivE l l' ∧ Agent.EvalEq p q :=
  (Agent.EvalEq.of_equivE (guardedElectionBody_equivE ns swap left right extra ch).symm).visible_transport h

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
