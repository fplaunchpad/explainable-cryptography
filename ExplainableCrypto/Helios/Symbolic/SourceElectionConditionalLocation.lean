import ExplainableCrypto.Helios.Symbolic.SourceConditionalLocation
import ExplainableCrypto.Helios.Symbolic.SourceElectionCommunicationMatching

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type} {n : Nat}

theorem collectBallots_no_ready_conditional (n : Nat) (ch : Channels) (remaining : Nat)
    (key first second : Term V) (others : List (Term V)) :
    ¬ (collectBallots n ch remaining key first second others).HasConditional := by
  cases remaining <;> simp [collectBallots,boardFinish,Agent.HasConditional]

/-- No range or freshness premise is needed for this exact syntactic location.
An exhausted input phase is an output, so it still has no ready conditional. -/
theorem residual_hasConditional_iff (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (phase : Process.Phase) :
    (residual ns swap left right extra ch phase).HasConditional ↔
      ∃ rs r, phase = .check rs r := by
  cases phase <;> simp [residual,electionBody,boardStart,boardSecond,boardFinish,
    trusteeAgent,Agent.HasConditional,collectBallots_no_ready_conditional]

theorem source_conditional_requires_check (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (phase : Process.Phase) {a b : Named (Fin phase.handles)}
    (ha : a.Interprets NameAssignment.literal (sourceView ns swap left right phase).value
      (residual ns swap left right extra ch phase)) (taken : Bool)
    (h : Named.InternalStep (.conditional taken) a b) :
    ∃ rs r, phase = .check rs r :=
  (residual_hasConditional_iff ns swap left right extra ch phase).mp
    (h.conditional_interprets_ready taken rfl NameAssignment.literal _ ha)

theorem source_reduction_communication_or_check (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (phase : Process.Phase) {a b : Named (Fin phase.handles)}
    (ha : a.Interprets NameAssignment.literal (sourceView ns swap left right phase).value
      (residual ns swap left right extra ch phase)) (h : Named.Reduction a b) :
    Named.InternalStep .communication a b ∨ ∃ rs r, phase = .check rs r := by
  obtain ⟨kind,hk⟩ := h.classify
  cases kind with
  | communication => exact .inl hk
  | conditional taken => exact .inr (source_conditional_requires_check ns swap left right extra ch phase ha taken hk)

/-- The arbitrary original source reduction is classified by the proof.
Only the explicitly identified check phase needs the remaining guard argument. -/
theorem source_reduction_communication_of_not_check (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (phase : Process.Phase) {a b : Named (Fin phase.handles)}
    (ha : a.Interprets NameAssignment.literal (sourceView ns swap left right phase).value
      (residual ns swap left right extra ch phase))
    (hn : ∀ rs r, phase ≠ .check rs r) (h : Named.Reduction a b) :
    Named.InternalStep .communication a b := by
  rcases source_reduction_communication_or_check ns swap left right extra ch phase ha h with hc | ⟨rs,r,he⟩
  · exact hc
  · exact (hn rs r he).elim

theorem reachable_source_noncheck_internal_matching (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (extra : Nat)
    (ch : Channels) (hc : ch.Fresh) (phase : Process.Phase)
    (hr : Process.Reachable ns swap left right extra phase)
    (hn : ∀ rs r, phase ≠ .check rs r)
    {a b d : Named (Fin phase.handles)}
    (ha : Named.Structural
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch phase)) a)
    (hd : Named.Structural
      (Named.restrictedState ch.privateChannels (sourceState ns swap' left right extra ch phase)) d)
    (h : Named.Reduction a b) :
    ∃ (next : Process.Phase) (q : ScopedState ns.restricted phase.handles),
      Process.Reachable ns swap left right extra next ∧
      Named.Reduction d (Named.restrictedState ch.privateChannels q) ∧
      q.frame = sourceView ns swap' left right phase ∧
      q.body = residual ns swap' left right extra ch next ∧
      b.Interprets NameAssignment.literal (sourceView ns swap left right phase).value
        (residual ns swap left right extra ch next) ∧
      Named.StaticEq b (Named.restrictedState ch.privateChannels q) :=
  reachable_source_communication_matching ns hf swap swap' left right extra ch hc phase hr ha hd
    (source_reduction_communication_of_not_check ns swap left right extra ch phase
      (ha.canonical_interprets _) hn h)

/-- Quiet interpreted bodies without a ready guard exclude every original
Named reduction, including arbitrary structural paths. -/
theorem Named.no_reduction_of_quiet_interpretation {a b : Named V}
    (ρ : NameAssignment) (env : V → Ground) {p : Agent Empty}
    (ha : a.Interprets ρ env p) (hn : ¬ p.HasConditional)
    (ht : ∀ q, ¬ Agent.Tau p q) : ¬ Named.Reduction a b := by
  intro h
  obtain ⟨q,hq,_⟩ := h.interprets_of_no_conditional ρ env ha hn
  exact ht q hq

theorem named_rejected_no_reduction (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (rs : List (Recipe 3)) {a b : Named (Fin 3)}
    (ha : Named.Structural
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch (.rejected rs))) a) :
    ¬ Named.Reduction a b :=
  Named.no_reduction_of_quiet_interpretation NameAssignment.literal _
    (p := residual ns swap left right extra ch (.rejected rs))
    (ha.canonical_interprets _) (by simp [residual,trusteeAgent,Agent.HasConditional])
    (residual_rejected_no_tau ns swap left right extra ch rs)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
