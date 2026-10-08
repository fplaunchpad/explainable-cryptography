import ExplainableCrypto.Helios.Symbolic.SourceCoordinatedInput

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- A raw input refreshes the same coordinates in both vote worlds, reaches its
actual check phase, and has a literal-label match from the fresh canonical
partner. Construction of that action in an arbitrary related raw partner is
not assumed or concluded. -/
theorem source_coordinated_common_input_next (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (e k : Nat ≃ Nat) (phase : Process.Phase) (hr : Process.Reachable ns swap left right extra phase)
    {a b d : Named (Fin phase.handles)}
    (ha : Named.JointOpening a (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k))
    (hd : Named.JointOpening d (Named.mappedState ch.privateChannels (sourceState ns swap' left right extra ch phase) e k))
    {c : Nat} {r : Recipe phase.handles} (h : Named.FreeStep a (.input c r) b) :
    ∃ (f l : Nat ≃ Nat) (rs : List (Recipe 3)) (s : Recipe 3),
      phase = .input rs ∧ HEq (r.mapNames (e.trans f).symm) s ∧ s.Public ns.restricted ∧
      c = (k.trans l) (ch.voter (rs.length+2)) ∧
      Process.Step ns swap left right extra phase (.input (rs.length+2) s) (.check rs s) ∧
      Process.Reachable ns swap left right extra (.check rs s) ∧
      CoordinatedPhaseOpening ns swap left right extra ch (e.trans f) (k.trans l) (.check rs s) b ∧
      Named.JointOpening a (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) (e.trans f) (k.trans l)) ∧
      Named.JointOpening d (Named.mappedState ch.privateChannels (sourceState ns swap' left right extra ch phase) (e.trans f) (k.trans l)) ∧
      ((sourceView ns swap left right phase).mapNames (e.trans f)).StaticEq
        ((sourceView ns swap' left right phase).mapNames (e.trans f)) ∧
      ∃ t : Named (Fin phase.handles),
        Named.FreeStep (Named.mappedState ch.privateChannels (sourceState ns swap' left right extra ch phase) (e.trans f) (k.trans l))
          (.input c r) t ∧
        CoordinatedPhaseOpening ns swap' left right extra ch (e.trans f) (k.trans l) (.check rs s) t := by
  have hs : (sourceView ns swap left right phase).StaticEq (sourceView ns swap' left right phase) := by
    have he := reachable_source_view_staticEq hf (hr.swap hf false)
    cases swap <;> cases swap'
    · exact .refl _
    · exact he
    · exact he.symm
    · exact .refl _
  obtain ⟨f,l,_,_,_,hpub,_,_,ha',hd',_,_⟩ := ha.common_fresh_input
    ((sourceState ns swap left right extra ch phase).mapNames e k)
    ((sourceState ns swap' left right extra ch phase).mapNames e k) hd (hs.mapNames e) h
    (Agent.input_determinism_mapNames _ (residual_visible_input_deterministic ns swap left right extra ch hc phase) e k)
  have ha'' : Named.JointOpening a (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) (e.trans f) (k.trans l)) := by
    rw [← Named.mappedState_comp]
    exact ha'
  have hd'' : Named.JointOpening d (Named.mappedState ch.privateChannels (sourceState ns swap' left right extra ch phase) (e.trans f) (k.trans l)) := by
    rw [← Named.mappedState_comp]
    exact hd'
  have hpub' : r.Public (ns.restricted.image (e.trans f)) := by
    simpa only [Finset.image_image,Equiv.coe_trans] using hpub
  obtain ⟨rs,s,hphase,he,hp,hchannel,hstep,ht⟩ := source_coordinated_public_input_next ns swap left right extra ch hc
    (e.trans f) (k.trans l) phase hr.wellFormed.inRange ha'' h hpub'
  subst phase
  have hrecipe : s.mapNames (e.trans f) = r := by
    rw [← eq_of_heq he]
    exact Term.mapNames_inverse r (e.trans f).symm
  have hother : ScopedStep ch.privateChannels ns.restricted
      (sourceState ns swap' left right extra ch (.input rs)) (.input (ch.voter (rs.length+2)) s)
      (sourceState ns swap' left right extra ch (.check rs s)) :=
    .input _ _ _ ((Channels.voter_public_iff hc _).mpr (by omega)) hp
      (residual_visible_input ns swap' left right extra ch rs s hr.wellFormed.inRange)
  have hmapped : ScopedStep (ch.privateChannels.image (k.trans l)) (ns.restricted.image (e.trans f))
      ((sourceState ns swap' left right extra ch (.input rs)).mapNames (e.trans f) (k.trans l)) (.input c r)
      ((sourceState ns swap' left right extra ch (.check rs s)).mapNames (e.trans f) (k.trans l)) := by
    have hh := hother.mapNames (e.trans f) (k.trans l)
    change ScopedStep _ _ _ (.input ((k.trans l) (ch.voter (rs.length+2))) (s.mapNames (e.trans f))) _ at hh
    rw [← hchannel,hrecipe] at hh
    exact hh
  exact ⟨f,l,rs,s,rfl,he,hp,hchannel,hstep,hr.tail ⟨_,hstep⟩,ht,ha'',hd'',hs.mapNames (e.trans f),
    _,Named.restricted_input_derivable _ _ _ _ hmapped,CoordinatedPhaseOpening.canonical⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
