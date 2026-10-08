import ExplainableCrypto.Helios.Symbolic.SourceFrameReindexing

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

/-- One relation for all original actions. Every pair carries actual execution
provenance, a reached historical phase, common name/handle coordinates and both
full current presentations. The existential voting order makes it symmetric. -/
def SourceElectionRelation {n : Nat} (origin : Bool → Named (Fin 1)) (ns : Names n)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    {handles : Nat} (a b : Named (Fin handles)) : Prop :=
  ∃ (swap swap' : Bool) (phase : Process.Phase) (i : Fin handles ≃ Fin phase.handles) (e k : Nat ≃ Nat),
    Process.Reachable ns swap left right extra phase ∧
    Process.Reachable ns swap' left right extra phase ∧
    Named.Execution (origin swap) a ∧ Named.Execution (origin swap') b ∧
    Named.JointOpening (a.rename i)
      (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k) ∧
    Named.JointOpening (b.rename i)
      (Named.mappedState ch.privateChannels (sourceState ns swap' left right extra ch phase) e k) ∧
    (a.rename i).RepresentsFrame (ch.privateChannels.image k) ((sourceView ns swap left right phase).mapNames e) ∧
    (b.rename i).RepresentsFrame (ch.privateChannels.image k) ((sourceView ns swap' left right phase).mapNames e)

namespace Named
variable {V W U : Type}

theorem rename_equiv_trans (a : Named V) (i : V ≃ W) (j : W ≃ U) :
    (a.rename i).rename j = a.rename (i.trans j) := rename_comp a i j

theorem rename_equiv_cancel (a : Named V) (i : V ≃ W) :
    (a.rename i).rename i.symm = a := by
  rw [rename_comp]
  have he : (i.symm : W → V) ∘ i = id := funext i.symm_apply_apply
  rw [he,rename_id]
end Named

namespace SourceElectionRelation
variable {n handles : Nat} {origin : Bool → Named (Fin 1)} {ns : Names n}
  {left right : CandidateSubstitution n Empty} {extra : Nat} {ch : Channels}
  {a b a' b' : Named (Fin handles)}

theorem symm (h : SourceElectionRelation origin ns left right extra ch a b) :
    SourceElectionRelation origin ns left right extra ch b a := by
  obtain ⟨s,t,p,i,e,k,hr,hr',ha,hb,hja,hjb,hpa,hpb⟩ := h
  exact ⟨t,s,p,i,e,k,hr',hr,hb,ha,hjb,hja,hpb,hpa⟩

theorem staticEq (hf : ns.Fresh) (h : SourceElectionRelation origin ns left right extra ch a b) :
    Named.StaticEq a b := by
  obtain ⟨s,t,p,i,e,k,hr,_,_,_,_,_,hpa,hpb⟩ := h
  have hs := reachable_source_view_staticEq hf (hr.swap hf false)
  have hv : (sourceView ns s left right p).StaticEq (sourceView ns t left right p) := by
    cases s <;> cases t
    · exact .refl _
    · exact hs
    · exact hs.symm
    · exact .refl _
  have he := (Named.StaticEq.of_presentations hpa hpb (hv.mapNames e)).reindex i.symm
  simpa only [Named.rename_equiv_cancel] using he

theorem structural (h : SourceElectionRelation origin ns left right extra ch a b)
    (ha : Named.Structural a a') (hb : Named.Structural b b') :
    SourceElectionRelation origin ns left right extra ch a' b' := by
  obtain ⟨s,t,p,i,e,k,hr,hr',hxa,hxb,hja,hjb,hpa,hpb⟩ := h
  exact ⟨s,t,p,i,e,k,hr,hr',hxa.trans (.structural ha),hxb.trans (.structural hb),
    hja.structural_left (ha.rename i i.injective),hjb.structural_left (hb.rename i i.injective),
    hpa.structural (ha.rename i i.injective),hpb.structural (hb.rename i i.injective)⟩

theorem reindex {j : Nat} (h : SourceElectionRelation origin ns left right extra ch a b)
    (u : Fin handles ≃ Fin j) :
    SourceElectionRelation origin ns left right extra ch (a.rename u) (b.rename u) := by
  obtain ⟨s,t,p,i,e,k,hr,hr',hxa,hxb,hja,hjb,hpa,hpb⟩ := h
  have eqn (x : Named (Fin handles)) : (x.rename u).rename (u.symm.trans i) = x.rename i := by
    rw [← Named.rename_equiv_trans,Named.rename_equiv_cancel]
  refine ⟨s,t,p,u.symm.trans i,e,k,hr,hr',hxa.trans (.reindex a u),hxb.trans (.reindex b u),?_,?_,?_,?_⟩ <;>
    rw [eqn]
  · exact hja
  · exact hjb
  · exact hpa
  · exact hpb

/-- The same relation, including both actual executions and observations,
survives every original internal reduction. -/
theorem internal (hf : ns.Fresh) (hc : ch.Fresh)
    (h : SourceElectionRelation origin ns left right extra ch a b) (ha : Named.Reduction a a') :
    ∃ b', Named.Reduction b b' ∧ SourceElectionRelation origin ns left right extra ch a' b' := by
  obtain ⟨s,t,p,i,e,k,hr,_,hxa,hxb,hja,hjb,hpa,hpb⟩ := h
  obtain ⟨next,hh,d,hd,hr,hr',hja',hjd,hpa',hpd,_⟩ := source_reachable_internal_match
    ns hf s t left right extra ch hc e k p hr hja hjb hpa hpb (ha.rename_equiv i)
  let u : Fin p.handles ≃ Fin next.handles := finCongr hh
  have hb : Named.Reduction b (d.rename i.symm) := by
    simpa only [Named.rename_equiv_cancel] using hd.rename_equiv i.symm
  have eqn : (d.rename i.symm).rename (i.trans u) = d.rename u := by
    rw [← Named.rename_equiv_trans]
    rw [show (d.rename i.symm).rename i = d from Named.rename_equiv_cancel d i.symm]
  refine ⟨d.rename i.symm,hb,s,t,next,i.trans u,e,k,hr,hr',hxa.trans (.internal ha),
    hxb.trans (.internal hb),?_,?_,?_,?_⟩
  · rw [← Named.rename_equiv_trans]; exact hja'
  · rw [eqn]; exact hjd
  · rw [← Named.rename_equiv_trans]; exact hpa'
  · rw [eqn]; exact hpd

/-- Exact raw public input labels survive the common coordinate change. -/
theorem input (hf : ns.Fresh) (hc : ch.Fresh)
    (h : SourceElectionRelation origin ns left right extra ch a b)
    {c : Nat} {r : Recipe handles} (ha : Named.FreeStep a (.input c r) a') :
    ∃ b', Named.FreeStep b (.input c r) b' ∧ SourceElectionRelation origin ns left right extra ch a' b' := by
  obtain ⟨s,t,p,i,e,k,hr,_,hxa,hxb,hja,hjb,hpa,hpb⟩ := h
  obtain ⟨f,l,next,hh,d,hd,hr,hr',hja',hjd,hpa',hpd,_⟩ := source_reachable_input_match
    ns hf s t left right extra ch hc e k p hr hja hjb hpa hpb (ha.rename_equiv i)
  let u : Fin p.handles ≃ Fin next.handles := finCongr hh
  have hb : Named.FreeStep b (.input c r) (d.rename i.symm) := by
    have hh := hd.rename_equiv i.symm
    simpa only [Named.rename_equiv_cancel,Extended.FreeLabel.rename,Term.subst_subst,Term.subst,
      Equiv.symm_apply_apply,Term.subst_var] using hh
  have eqn : (d.rename i.symm).rename (i.trans u) = d.rename u := by
    rw [← Named.rename_equiv_trans]
    rw [show (d.rename i.symm).rename i = d from Named.rename_equiv_cancel d i.symm]
  refine ⟨d.rename i.symm,hb,s,t,next,i.trans u,f,l,hr,hr',hxa.trans (.free ha),
    hxb.trans (.free hb),?_,?_,?_,?_⟩
  · rw [← Named.rename_equiv_trans]; exact hja'
  · rw [eqn]; exact hjd
  · rw [← Named.rename_equiv_trans]; exact hpa'
  · rw [eqn]; exact hpd

theorem no_handle_output (hf : ns.Fresh)
    (h : SourceElectionRelation origin ns left right extra ch a b)
    (c : Nat) (x : Fin handles) : ¬ Named.FreeStep a (.output c x) a' := by
  obtain ⟨s,_,p,i,e,k,hr,_,_,_,hja,_⟩ := h
  intro ha
  exact source_coordinated_no_handle_output ns hf s left right extra ch e k p hr hja c (i x) _
    (ha.rename_equiv i)

theorem free (hf : ns.Fresh) (hc : ch.Fresh)
    (h : SourceElectionRelation origin ns left right extra ch a b)
    {l : Extended.FreeLabel (Fin handles)} (ha : Named.FreeStep a l a') :
    ∃ b', Named.FreeStep b l b' ∧ SourceElectionRelation origin ns left right extra ch a' b' := by
  cases l with
  | input => exact h.input hf hc ha
  | output c x => exact (h.no_handle_output hf c x ha).elim

/-- The bound target keeps Option's fresh coordinate and every old handle;
outputHandle only enumerates that exact domain for the same relation. -/
theorem bound (hf : ns.Fresh) (hc : ch.Fresh)
    (h : SourceElectionRelation origin ns left right extra ch a b)
    {c : Nat} {target : Named (Option (Fin handles))} (ha : Named.BoundOutput a c target) :
    ∃ target', Named.BoundOutput b c target' ∧
      SourceElectionRelation origin ns left right extra ch
        (target.rename Extended.outputHandle) (target'.rename Extended.outputHandle) := by
  obtain ⟨s,t,p,i,e,k,hr,_,hxa,hxb,hja,hjb,hpa,hpb⟩ := h
  obtain ⟨next,hh,d,hd,hr,hr',hja',hjd,hpa',hpd,_⟩ := source_reachable_bound_match
    ns hf s t left right extra ch hc e k p hr hja hjb hpa hpb (ha.rename_equiv i)
  let oi := Equiv.optionCongr i
  let v : Option (Fin p.handles) ≃ Fin next.handles := Extended.outputHandle.trans (finCongr hh)
  let u : Fin (handles+1) ≃ Fin next.handles := Extended.outputHandle.symm.trans (oi.trans v)
  let target' := d.rename oi.symm
  have hb : Named.BoundOutput b c target' := by
    have hb' := hd.rename_equiv i.symm
    rw [Named.rename_equiv_cancel] at hb'
    exact hb'
  have eqn (x : Named (Option (Fin handles))) :
      (x.rename Extended.outputHandle).rename u = (x.rename oi).rename v := by
    dsimp only [u]
    rw [← Named.rename_equiv_trans,Named.rename_equiv_cancel,← Named.rename_equiv_trans]
  have eqn' : (target'.rename Extended.outputHandle).rename u = d.rename v := by
    rw [eqn]
    change ((d.rename oi.symm).rename oi).rename v = d.rename v
    rw [show (d.rename oi.symm).rename oi = d from Named.rename_equiv_cancel d oi.symm]
  refine ⟨target',hb,s,t,next,u,e,k,hr,hr',
    (hxa.trans (.bound ha)).trans (.reindex target Extended.outputHandle),
    (hxb.trans (.bound hb)).trans (.reindex target' Extended.outputHandle),?_,?_,?_,?_⟩
  · rw [eqn,← Named.rename_equiv_trans]; exact hja'
  · rw [eqn',← Named.rename_equiv_trans]; exact hjd
  · rw [eqn,← Named.rename_equiv_trans]; exact hpa'
  · rw [eqn',← Named.rename_equiv_trans]; exact hpd

/-- Actual scoped initial elections supply every relation field from the
historical freshness conditions; no correspondence hypothesis is supplied. -/
theorem initial (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (hl : NoncesFreshFor ns left.value)
    (hr : NoncesFreshFor ns right.value) (extra : Nat) (ch : Channels) :
    SourceElectionRelation (fun s => scopedVoterElection ns s left right extra ch)
      ns left right extra ch (scopedVoterElection ns swap left right extra ch)
        (scopedVoterElection ns swap' left right extra ch) := by
  have hj (s : Bool) : Named.JointOpening
      ((scopedVoterElection ns s left right extra ch).rename (Equiv.refl (Fin 1)))
      (Named.mappedState ch.privateChannels (sourceState ns s left right extra ch .start)
        (Equiv.refl Nat) (Equiv.refl Nat)) := by
    change Named.JointOpening ((scopedVoterElection ns s left right extra ch).rename id) _
    rw [Named.rename_id]
    have hid := Named.mappedState_identity ch.privateChannels
      (sourceState ns s left right extra ch .start)
    exact (congrArg (Named.JointOpening (scopedVoterElection ns s left right extra ch)) hid).mpr
      ((scopedVoterElection_normalizes ns hf s left right hl hr extra ch).symm.jointOpening _)
  have hp (s : Bool) :
      ((scopedVoterElection ns s left right extra ch).rename (Equiv.refl (Fin 1))).RepresentsFrame
        (ch.privateChannels.image (Equiv.refl Nat))
        ((sourceView ns s left right .start).mapNames (Equiv.refl Nat)) := by
    change ((scopedVoterElection ns s left right extra ch).rename id).RepresentsFrame
      (ch.privateChannels.image id) ((sourceView ns s left right .start).mapNames id)
    simpa only [Named.rename_id,Named.RepresentsFrame,Named.canonicalFrame,Extended.activeFrame,
      Extended.frameEntries,Frame.mapNames,Term.mapNames_id,Finset.image_id] using
      scopedVoterElection_represents ns hf s left right hl hr extra ch
  exact ⟨swap,swap',.start,Equiv.refl _,Equiv.refl _,Equiv.refl _,.refl,.refl,
    .refl _,.refl _,hj swap,hj swap',hp swap,hp swap'⟩

end SourceElectionRelation
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
