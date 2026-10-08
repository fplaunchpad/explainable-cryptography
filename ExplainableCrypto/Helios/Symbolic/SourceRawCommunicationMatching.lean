import ExplainableCrypto.Helios.Symbolic.SourceCommunicationAvailability

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Process
variable {n : Nat}

/-- The two conditional choices are disjoint; every other internal phase has
one prescribed control successor. No cryptographic decision procedure is used. -/
theorem Step.tau_deterministic {ns : Names n} {swap : Bool}
    {left right : CandidateSubstitution n Empty} {extra : Nat} {p q r : Phase}
    (h : Step ns swap left right extra p .tau q) (j : Step ns swap left right extra p .tau r) : q = r := by
  cases h <;> cases j <;> first | rfl | contradiction

end ExplainableCrypto.Helios.Symbolic.Historical.General.Process

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- Outside the check phase, an actual raw internal action has an actual raw
partner action with the same successor phase and complete static observations.
The check-phase hypothesis is explicit; its guard-grounding branch remains open. -/
theorem source_reachable_internal_match_of_no_conditional (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (e k : Nat ≃ Nat) (phase : Process.Phase) (hr : Process.Reachable ns swap left right extra phase)
    (hn : ¬ ∃ rs r, phase = .check rs r)
    {a b d : Named (Fin phase.handles)}
    (ha : Named.JointOpening a (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k))
    (hd : Named.JointOpening d (Named.mappedState ch.privateChannels (sourceState ns swap' left right extra ch phase) e k))
    (hpa : a.RepresentsFrame (ch.privateChannels.image k) ((sourceView ns swap left right phase).mapNames e))
    (hpd : d.RepresentsFrame (ch.privateChannels.image k) ((sourceView ns swap' left right phase).mapNames e))
    (h : Named.Reduction a b) :
    ∃ (next : Process.Phase) (hh : phase.handles = next.handles) (t : Named (Fin phase.handles)),
      Named.Reduction d t ∧
      Process.Reachable ns swap left right extra next ∧
      Process.Reachable ns swap' left right extra next ∧
      Named.JointOpening (b.rename (Fin.cast hh))
        (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch next) e k) ∧
      Named.JointOpening (t.rename (Fin.cast hh))
        (Named.mappedState ch.privateChannels (sourceState ns swap' left right extra ch next) e k) ∧
      (b.rename (Fin.cast hh)).RepresentsFrame (ch.privateChannels.image k)
        ((sourceView ns swap left right next).mapNames e) ∧
      (t.rename (Fin.cast hh)).RepresentsFrame (ch.privateChannels.image k)
        ((sourceView ns swap' left right next).mapNames e) ∧
      Named.StaticEq (b.rename (Fin.cast hh)) (t.rename (Fin.cast hh)) := by
  obtain ⟨next,hh,hs,hreach,hb,hpb⟩ := source_coordinated_internal_presented_next ns swap left right extra ch hc
    e k phase hr ha hpa h
  have hother := hs.swap hf swap' hr.wellFormed.publicHistory hr.wellFormed.pendingPublic
  have hτ := (residual_tau_step ns swap' left right extra ch hother).mapNames e k
  have hn' : ¬ ((residual ns swap' left right extra ch phase).mapNames e k).HasConditional := by
    intro hready
    exact hn ((residual_hasConditional_iff ns swap' left right extra ch phase).mp
      ((Agent.hasConditional_mapNames _ e k).mp hready))
  obtain ⟨t,ht⟩ := hd.internal_available_of_no_conditional hτ hn'
  obtain ⟨next',hh',hs',_,htjoint,hpt⟩ := source_coordinated_internal_presented_next ns swap' left right extra ch hc
    e k phase (hr.swap hf swap') hd hpd ht
  have hnext : next' = next := hs'.tau_deterministic hother
  subst next'
  refine ⟨next,hh,t,ht,hreach,hreach.swap hf swap',hb,htjoint,hpb,hpt,?_⟩
  have he := reachable_source_view_staticEq hf (hreach.swap hf false)
  have hsview : (sourceView ns swap left right next).StaticEq (sourceView ns swap' left right next) := by
    cases swap <;> cases swap'
    · exact .refl _
    · exact he
    · exact he.symm
    · exact .refl _
  exact Named.StaticEq.of_presentations hpb hpt (hsview.mapNames e)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
