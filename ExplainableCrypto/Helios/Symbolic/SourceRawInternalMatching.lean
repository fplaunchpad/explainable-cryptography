import ExplainableCrypto.Helios.Symbolic.SourcePresentedInternalAvailability

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- Every reachable internal action, including acceptance and rejection, has
an actual raw partner action. Both complete successor presentations and the
shared reached phase are preserved. -/
theorem source_reachable_internal_match (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (e k : Nat ≃ Nat) (phase : Process.Phase) (hr : Process.Reachable ns swap left right extra phase)
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
  obtain ⟨t,ht⟩ := hd.internal_available hpd hτ
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
