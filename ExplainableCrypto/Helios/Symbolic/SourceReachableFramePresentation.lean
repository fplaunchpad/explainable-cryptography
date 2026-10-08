import ExplainableCrypto.Helios.Symbolic.SourceOutputFramePresentation
import ExplainableCrypto.Helios.Symbolic.SourceInputPresentationClosure
import ExplainableCrypto.Helios.Symbolic.SourceReachableElectionPhases

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat} {V W : Type}

/-- Alignment changes the existential output policy to the reached phase's
actual policy after transporting the entire fresh handle domain. -/
theorem CoordinatedPhaseOpening.presented {handles : Nat} {ns : Names n} {swap : Bool}
    {left right : CandidateSubstitution n Empty} {extra : Nat} {ch : Channels}
    {e k : Nat ≃ Nat} {phase : Process.Phase} {a : Named (Fin handles)}
    (h : CoordinatedPhaseOpening ns swap left right extra ch e k phase a)
    {policy channels : Finset Nat} {φ : Frame policy handles}
    (hp : a.RepresentsFrame channels φ) :
    ∃ hh : handles = phase.handles,
      Named.JointOpening (a.rename (Fin.cast hh))
        (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k) ∧
      (a.rename (Fin.cast hh)).RepresentsFrame (ch.privateChannels.image k)
        ((sourceView ns swap left right phase).mapNames e) := by
  obtain ⟨hh,hj⟩ := h
  subst handles
  have he : Fin.cast (Eq.refl phase.handles) = (id : Fin phase.handles → Fin phase.handles) := rfl
  simp only [he,Named.rename_id] at hj
  refine ⟨rfl,?_,?_⟩
  · simpa only [he,Named.rename_id] using hj
  · simpa only [he,Named.rename_id,ScopedState.mapNames,sourceState] using hj.align_presentation hp

/-- Every actual execution preserves both the complete ground presentation and
the phase witness. No forest, capture, freshness or target presentation is
supplied by the caller; the current actual presentation is the induction base. -/
theorem Named.Execution.election_presented_phase (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    {a : Named V} {b : Named W} (h : Named.Execution a b)
    (phase : Process.Phase) (e k : Nat ≃ Nat) (i : V ≃ Fin phase.handles)
    (hr : Process.Reachable ns swap left right extra phase)
    (ha : Named.JointOpening (a.rename i)
      (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k))
    (hp : (a.rename i).RepresentsFrame (ch.privateChannels.image k)
      ((sourceView ns swap left right phase).mapNames e)) :
    ∃ (next : Process.Phase) (f l : Nat ≃ Nat) (j : W ≃ Fin next.handles),
      Process.Reachable ns swap left right extra next ∧
      Named.JointOpening (b.rename j)
        (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch next) f l) ∧
      (b.rename j).RepresentsFrame (ch.privateChannels.image l)
        ((sourceView ns swap left right next).mapNames f) := by
  induction h generalizing phase e k with
  | refl => exact ⟨phase,e,k,i,hr,ha,hp⟩
  | structural h => exact ⟨phase,e,k,i,hr,ha.structural_left (h.rename i i.injective),
      hp.structural (h.rename i i.injective)⟩
  | internal h =>
    obtain ⟨next,hh,_,ht,hb,hpb⟩ := source_coordinated_internal_presented_next ns swap left right extra ch hc
      e k phase hr ha hp (h.rename_equiv i)
    refine ⟨next,e,k,i.trans (finCongr hh),ht,?_,?_⟩
    · simpa only [Named.rename_comp,Equiv.coe_trans,finCongr,Equiv.coe_fn_mk] using hb
    · simpa only [Named.rename_comp,Equiv.coe_trans,finCongr,Equiv.coe_fn_mk] using hpb
  | free h =>
    rename_i U a b label
    cases label with
    | output c x =>
      exact (source_coordinated_no_handle_output ns hf swap left right extra ch e k phase hr ha
        c (i x) (b.rename i) (h.rename_equiv i)).elim
    | input c r =>
      obtain ⟨f,l,rs,s,_,_,_,_,_,ht,hb,hpb,_,_,_⟩ := source_coordinated_input_presented_next
        ns hf swap swap left right extra ch hc e k phase hr ha ha hp hp (h.rename_equiv i)
      obtain ⟨hh,hb,hpb⟩ := hb.presented hpb
      refine ⟨.check rs s,e.trans f,k.trans l,i.trans (finCongr hh),ht,?_,?_⟩
      · simpa only [Named.rename_comp,Equiv.coe_trans,finCongr,Equiv.coe_fn_mk] using hb
      · simpa only [Named.rename_comp,Equiv.coe_trans,finCongr,Equiv.coe_fn_mk] using hpb
  | bound h =>
    have hout := h.rename_equiv i
    obtain ⟨handle,m,next,_,hs,_,hb⟩ := source_coordinated_output_next ns swap left right extra ch hc
      e k phase hr.wellFormed.inRange ha hout
    obtain ⟨policy,channels,φ,hpb⟩ := hout.exists_frame_presentation hp
    obtain ⟨hh,hb,hpb⟩ := hb.presented hpb
    refine ⟨next,e,k,((Equiv.optionCongr i).trans Extended.outputHandle).trans (finCongr hh),
      hr.tail ⟨_,hs⟩,?_,?_⟩
    · simpa only [Named.rename_comp,Equiv.coe_trans,finCongr,Equiv.coe_fn_mk,Equiv.optionCongr,
        Function.comp_assoc] using hb
    · simpa only [Named.rename_comp,Equiv.coe_trans,finCongr,Equiv.coe_fn_mk,Equiv.optionCongr,
        Function.comp_assoc] using hpb
  | reindex a j =>
    refine ⟨phase,e,k,j.symm.trans i,hr,?_,?_⟩
    · have he : (j.symm.trans i : _ → _) ∘ j = i := by
        funext v
        exact congrArg i (j.symm_apply_apply v)
      simpa only [Named.rename_comp,he] using ha
    · have he : (j.symm.trans i : _ → _) ∘ j = i := by
        funext v
        exact congrArg i (j.symm_apply_apply v)
      simpa only [Named.rename_comp,he] using hp
  | trans h j ih ij =>
    obtain ⟨next,f,l,k',ht,hb,hpb⟩ := ih phase e k i hr ha hp
    exact ij next f l k' ht hb hpb

/-- Actual scoped elections supply the initial presentation, parameter freshness
and phase witness for arbitrary finite original executions. This discharges
reachable-state frame reconstruction, while raw-partner action availability is
still a separate B9 obligation. -/
theorem source_reachable_frame_presentation (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (hl : NoncesFreshFor ns left.value)
    (hr : NoncesFreshFor ns right.value) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    {a : Named V} (h : Named.Execution (scopedVoterElection ns swap left right extra ch) a) :
    ∃ (phase : Process.Phase) (e k : Nat ≃ Nat) (i : V ≃ Fin phase.handles),
      Process.Reachable ns swap left right extra phase ∧
      Named.JointOpening (a.rename i)
        (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k) ∧
      (a.rename i).RepresentsFrame (ch.privateChannels.image k)
        ((sourceView ns swap left right phase).mapNames e) := by
  apply h.election_presented_phase ns hf swap left right extra ch hc .start
    (Equiv.refl Nat) (Equiv.refl Nat) (Equiv.refl (Fin 1)) .refl
  · change Named.JointOpening ((scopedVoterElection ns swap left right extra ch).rename id)
      (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch .start)
        (Equiv.refl Nat) (Equiv.refl Nat))
    rw [Named.rename_id]
    have hid := Named.mappedState_identity ch.privateChannels
      (sourceState ns swap left right extra ch .start)
    exact (congrArg (Named.JointOpening (scopedVoterElection ns swap left right extra ch)) hid).mpr
      ((scopedVoterElection_normalizes ns hf swap left right hl hr extra ch).symm.jointOpening
        (sourceState ns swap left right extra ch .start))
  · change ((scopedVoterElection ns swap left right extra ch).rename id).RepresentsFrame
      (ch.privateChannels.image id) ((sourceView ns swap left right .start).mapNames id)
    simpa only [Named.rename_id,Named.RepresentsFrame,Named.canonicalFrame,Extended.activeFrame,Extended.frameEntries,Frame.mapNames,
      Term.mapNames_id,Finset.image_id] using
      scopedVoterElection_represents ns hf swap left right hl hr extra ch

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
