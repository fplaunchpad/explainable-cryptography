import ExplainableCrypto.Helios.Symbolic.SourceCommunicationInterpretation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

theorem source_communication_interpreted (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) (hr : phase.inRange extra)
    {a b : Named (Fin phase.handles)}
    (ha : a.Interprets NameAssignment.literal (sourceView ns swap left right phase).value
      (residual ns swap left right extra ch phase))
    (h : Named.InternalStep .communication a b) :
    ∃ next, Process.Step ns swap left right extra phase .tau next ∧
      b.Interprets NameAssignment.literal (sourceView ns swap left right phase).value
        (residual ns swap left right extra ch next) := by
  obtain ⟨q,hq,hb⟩ := h.communication_interprets NameAssignment.literal _ ha
  obtain ⟨next,hs,he⟩ := residual_tau_complete ns swap left right extra ch hc phase hr hq
  exact ⟨next,hs,hb.congr (.of_parEq he)⟩

/-- Communication matching uses an actual source action in the other world,
retains the full reached body on the original raw target, and supplies the
two targets' Named static-equivalence witness. Conditional source actions
are not assumed to be communications. -/
theorem reachable_source_communication_matching (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (extra : Nat)
    (ch : Channels) (hc : ch.Fresh) (phase : Process.Phase)
    (hr : Process.Reachable ns swap left right extra phase)
    {a b d : Named (Fin phase.handles)}
    (ha : Named.Structural
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch phase)) a)
    (hd : Named.Structural
      (Named.restrictedState ch.privateChannels (sourceState ns swap' left right extra ch phase)) d)
    (h : Named.InternalStep .communication a b) :
    ∃ (next : Process.Phase) (q : ScopedState ns.restricted phase.handles),
      Process.Reachable ns swap left right extra next ∧
      Named.Reduction d (Named.restrictedState ch.privateChannels q) ∧
      q.frame = sourceView ns swap' left right phase ∧
      q.body = residual ns swap' left right extra ch next ∧
      b.Interprets NameAssignment.literal (sourceView ns swap left right phase).value
        (residual ns swap left right extra ch next) ∧
      Named.StaticEq b (Named.restrictedState ch.privateChannels q) := by
  obtain ⟨next,hs,hb⟩ := source_communication_interpreted ns swap left right extra ch hc
    phase hr.wellFormed.inRange (ha.canonical_interprets _) h
  have hs' := hs.swap hf swap' hr.wellFormed.publicHistory hr.wellFormed.pendingPublic
  let q : ScopedState ns.restricted phase.handles :=
    ⟨sourceView ns swap' left right phase,residual ns swap' left right extra ch next⟩
  have hq : ScopedStep ch.privateChannels ns.restricted
      (sourceState ns swap' left right extra ch phase) .tau q :=
    .tau _ (residual_tau_step ns swap' left right extra ch hs')
  have hred : Named.Reduction d (Named.restrictedState ch.privateChannels q) :=
    .congr hd.symm (Named.restricted_tau_derivable _ _ hq) (.refl _)
  have hframes : (sourceView ns swap left right phase).StaticEq (sourceView ns swap' left right phase) := by
    have he := reachable_source_view_staticEq hf (hr.swap hf false)
    cases swap <;> cases swap'
    · exact .refl _
    · exact he
    · exact he.symm
    · exact .refl _
  have hp := ((Named.restrictedState_represents (sourceState ns swap left right extra ch phase)).structural ha).internal h.reduction
  exact ⟨next,q,hr.tail ⟨.tau,hs⟩,hred,rfl,rfl,hb,
    .of_presentations hp (Named.restrictedState_represents q) hframes⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
