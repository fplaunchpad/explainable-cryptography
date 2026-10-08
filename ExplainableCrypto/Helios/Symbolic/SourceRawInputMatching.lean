import ExplainableCrypto.Helios.Symbolic.SourceJointVisibleAvailability

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- An arbitrary actual input has an action from the related raw partner, with
the exact same recipe and jointly refreshed policies. Both actual successors
retain their reached phase, full presentation and static observations. -/
theorem source_reachable_input_match (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (e k : Nat ≃ Nat) (phase : Process.Phase) (hr : Process.Reachable ns swap left right extra phase)
    {a b d : Named (Fin phase.handles)}
    (ha : Named.JointOpening a (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k))
    (hd : Named.JointOpening d (Named.mappedState ch.privateChannels (sourceState ns swap' left right extra ch phase) e k))
    (hpa : a.RepresentsFrame (ch.privateChannels.image k) ((sourceView ns swap left right phase).mapNames e))
    (hpd : d.RepresentsFrame (ch.privateChannels.image k) ((sourceView ns swap' left right phase).mapNames e))
    {c : Nat} {r : Recipe phase.handles} (h : Named.FreeStep a (.input c r) b) :
    ∃ (f l : Nat ≃ Nat) (next : Process.Phase) (hh : phase.handles = next.handles)
      (t : Named (Fin phase.handles)),
      Named.FreeStep d (.input c r) t ∧
      Process.Reachable ns swap left right extra next ∧
      Process.Reachable ns swap' left right extra next ∧
      Named.JointOpening (b.rename (Fin.cast hh))
        (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch next) f l) ∧
      Named.JointOpening (t.rename (Fin.cast hh))
        (Named.mappedState ch.privateChannels (sourceState ns swap' left right extra ch next) f l) ∧
      (b.rename (Fin.cast hh)).RepresentsFrame (ch.privateChannels.image l)
        ((sourceView ns swap left right next).mapNames f) ∧
      (t.rename (Fin.cast hh)).RepresentsFrame (ch.privateChannels.image l)
        ((sourceView ns swap' left right next).mapNames f) ∧
      Named.StaticEq b t := by
  obtain ⟨f,l,rs,s,hphase,he,hpub,hchannel,hstage,hreach,hb,hpb,hpd',hd',_⟩ :=
    source_coordinated_input_presented_next ns hf swap swap' left right extra ch hc e k phase hr ha hd hpa hpd h
  subst phase
  have hrecipe : s.mapNames (e.trans f) = r := by
    rw [← eq_of_heq he]
    exact Term.mapNames_inverse r (e.trans f).symm
  have hother : ScopedStep ch.privateChannels ns.restricted
      (sourceState ns swap' left right extra ch (.input rs)) (.input (ch.voter (rs.length+2)) s)
      (sourceState ns swap' left right extra ch (.check rs s)) :=
    .input _ _ _ ((Channels.voter_public_iff hc _).mpr (by omega)) hpub
      (residual_visible_input ns swap' left right extra ch rs s hr.wellFormed.inRange)
  have hmapped := hother.mapNames (e.trans f) (k.trans l)
  change ScopedStep _ _ _ (.input ((k.trans l) (ch.voter (rs.length+2))) (s.mapNames (e.trans f))) _ at hmapped
  rw [← hchannel,hrecipe] at hmapped
  obtain ⟨hchan,hrec,_,hv⟩ := (scoped_input_iff _ _ _ _).mp hmapped
  obtain ⟨t,ht⟩ := hd'.input_available hchan hv.hasInput r
  have hj := hd'.public_input_target ht hrec (fun q hq =>
    (Agent.input_determinism_mapNames _
      (residual_visible_input_deterministic ns swap' left right extra ch hc (.input rs))
      (e.trans f) (k.trans l)) _ _ _ _ hq hv)
  have hpt := hpd'.free ht
  obtain ⟨hh,hb,hpb⟩ := hb.presented hpb
  have hbeq : b.rename (Fin.cast hh) = b := by
    change b.rename id = b
    exact Named.rename_id b
  have hteq : t.rename (Fin.cast hh) = t := by
    change t.rename id = t
    exact Named.rename_id t
  refine ⟨e.trans f,k.trans l,.check rs s,hh,t,ht,hreach,hreach.swap hf swap',hb,?_,hpb,?_,?_⟩
  · rw [hteq]
    simpa only [Named.mappedState,ScopedState.mapNames,sourceState,sourceView,Process.Phase.handles] using hj
  · rw [hteq]
    exact hpt
  · have hs := reachable_source_view_staticEq hf (hreach.swap hf false)
    have heq : (sourceView ns swap left right (.check rs s)).StaticEq
        (sourceView ns swap' left right (.check rs s)) := by
      cases swap <;> cases swap'
      · exact .refl _
      · exact hs
      · exact hs.symm
      · exact .refl _
    apply Named.StaticEq.of_presentations
      (by rw [hbeq] at hpb; exact hpb) hpt (heq.mapNames (e.trans f))

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
