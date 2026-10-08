import ExplainableCrypto.Helios.Symbolic.SourceFreshCanonicalInternal

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- All original Named internal actions, including check branches, correspond
to a stage step. The full raw target uses one coherently permuted frame/body. -/
theorem source_fresh_internal_interpreted (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) (hr : phase.inRange extra)
    {a b : Named (Fin phase.handles)}
    (ha : Named.Structural
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch phase)) a)
    (h : Named.Reduction a b) :
    ∃ (next : Process.Phase) (e k : Nat ≃ Nat),
      Process.Step ns swap left right extra phase .tau next ∧
      b.Interprets NameAssignment.literal ((sourceView ns swap left right phase).mapNames e).value
        ((residual ns swap left right extra ch next).mapNames e k) := by
  obtain ⟨e,k,q,hq,hb⟩ := h.canonical_tau (sourceState ns swap left right extra ch phase) ha
  obtain ⟨next,hs,he⟩ := residual_tau_complete ns swap left right extra ch hc phase hr hq
  exact ⟨next,e,k,hs,hb.congr (.of_parEq (he.mapNames e k))⟩

/-- An arbitrary actual Named internal reduction from a reached canonical
representative has an actual matching reduction in the other world and
statically equivalent raw targets. Interpretation is retained in fresh
coordinates; this theorem does not assert the next relation's closure. -/
theorem reachable_source_fresh_internal_matching (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (extra : Nat)
    (ch : Channels) (hc : ch.Fresh) (phase : Process.Phase)
    (hr : Process.Reachable ns swap left right extra phase)
    {a b d : Named (Fin phase.handles)}
    (ha : Named.Structural
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch phase)) a)
    (hd : Named.Structural
      (Named.restrictedState ch.privateChannels (sourceState ns swap' left right extra ch phase)) d)
    (h : Named.Reduction a b) :
    ∃ (next : Process.Phase) (q : ScopedState ns.restricted phase.handles) (e k : Nat ≃ Nat),
      Process.Reachable ns swap left right extra next ∧
      Named.Reduction d (Named.restrictedState ch.privateChannels q) ∧
      q.frame = sourceView ns swap' left right phase ∧
      q.body = residual ns swap' left right extra ch next ∧
      b.Interprets NameAssignment.literal ((sourceView ns swap left right phase).mapNames e).value
        ((residual ns swap left right extra ch next).mapNames e k) ∧
      Named.StaticEq b (Named.restrictedState ch.privateChannels q) := by
  obtain ⟨next,e,k,hs,hb⟩ := source_fresh_internal_interpreted ns swap left right extra ch hc
    phase hr.wellFormed.inRange ha h
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
  have hp := ((Named.restrictedState_represents (sourceState ns swap left right extra ch phase)).structural ha).internal h
  exact ⟨next,q,e,k,hr.tail ⟨.tau,hs⟩,hred,rfl,rfl,hb,
    .of_presentations hp (Named.restrictedState_represents q) hframes⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
