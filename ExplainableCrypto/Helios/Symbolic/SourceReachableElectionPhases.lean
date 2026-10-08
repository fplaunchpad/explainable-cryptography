import ExplainableCrypto.Helios.Symbolic.SourceExecutionHandleRenaming
import ExplainableCrypto.Helios.Symbolic.SourceCoordinatedFreshInput
import ExplainableCrypto.Helios.Symbolic.SourceCoordinatedOutput
import ExplainableCrypto.Helios.Symbolic.SourceElectionHandleExclusion
import ExplainableCrypto.Helios.Symbolic.SourceScopedElectionActions

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat} {V W : Type}

/-- Full source execution retains a reached historical phase. Coordinates may
refresh after each arbitrary input; the explicit bijection retains the entire
current handle domain across bound output and execution reindexing. This is
phase correspondence, not structural reconstruction or bisimilarity. -/
theorem Named.Execution.election_phase (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    {a : Named V} {b : Named W} (h : Named.Execution a b)
    (phase : Process.Phase) (e k : Nat ≃ Nat) (i : V ≃ Fin phase.handles)
    (hr : Process.Reachable ns swap left right extra phase)
    (ha : Named.JointOpening (a.rename i)
      (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k)) :
    ∃ (next : Process.Phase) (f l : Nat ≃ Nat) (j : W ≃ Fin next.handles),
      Process.Reachable ns swap left right extra next ∧
      Named.JointOpening (b.rename j)
        (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch next) f l) := by
  induction h generalizing phase e k with
  | refl => exact ⟨phase,e,k,i,hr,ha⟩
  | structural h => exact ⟨phase,e,k,i,hr,ha.structural_left (h.rename i i.injective)⟩
  | internal h =>
    obtain ⟨next,hh,hs,hb⟩ := source_coordinated_internal_next ns swap left right extra ch hc
      e k phase hr.wellFormed.inRange ha (h.rename_equiv i)
    refine ⟨next,e,k,i.trans (finCongr hh),hr.tail ⟨.tau,hs⟩,?_⟩
    simpa only [Named.rename_comp,Equiv.coe_trans,finCongr,Equiv.coe_fn_mk] using hb
  | free h =>
    rename_i U a b label
    cases label with
    | output c x =>
      exact (source_coordinated_no_handle_output ns hf swap left right extra ch e k phase hr ha
        c (i x) (b.rename i) (h.rename_equiv i)).elim
    | input c r =>
      obtain ⟨f,l,rs,s,_,_,_,_,_,ht,hb,_,_,_,_⟩ := source_coordinated_common_input_next
        ns hf swap swap left right extra ch hc e k phase hr ha ha (h.rename_equiv i)
      obtain ⟨hh,hb⟩ := hb
      refine ⟨.check rs s,e.trans f,k.trans l,i.trans (finCongr hh),ht,?_⟩
      simpa only [Named.rename_comp,Equiv.coe_trans,finCongr,Equiv.coe_fn_mk] using hb
  | bound h =>
    obtain ⟨handle,m,next,hpub,hs,_,hb⟩ := source_coordinated_output_next ns swap left right extra ch hc
      e k phase hr.wellFormed.inRange ha (h.rename_equiv i)
    obtain ⟨hh,hb⟩ := hb
    refine ⟨next,e,k,((Equiv.optionCongr i).trans Extended.outputHandle).trans (finCongr hh),
      hr.tail ⟨_,hs⟩,?_⟩
    simpa only [Named.rename_comp,Equiv.coe_trans,finCongr,Equiv.coe_fn_mk,Equiv.optionCongr,Equiv.coe_fn_mk,Function.comp_assoc] using hb
  | reindex a j =>
    refine ⟨phase,e,k,j.symm.trans i,hr,?_⟩
    have he : (j.symm.trans i : _ → _) ∘ j = i := by
      funext v
      exact congrArg i (j.symm_apply_apply v)
    simpa only [Named.rename_comp,he] using ha
  | trans h j ih ij =>
    obtain ⟨next,f,l,k',ht,hb⟩ := ih phase e k i hr ha
    exact ij next f l k' ht hb

/-- The actual scope-bearing election supplies the invariant's initial witness;
no caller-supplied program extraction or phase correspondence remains. -/
theorem scopedVoterElection_execution_phase (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (hl : NoncesFreshFor ns left.value)
    (hr : NoncesFreshFor ns right.value) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    {a : Named V} (h : Named.Execution (scopedVoterElection ns swap left right extra ch) a) :
    ∃ (phase : Process.Phase) (e k : Nat ≃ Nat) (i : V ≃ Fin phase.handles),
      Process.Reachable ns swap left right extra phase ∧
      Named.JointOpening (a.rename i)
        (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k) := by
  apply h.election_phase ns hf swap left right extra ch hc .start
    (Equiv.refl Nat) (Equiv.refl Nat) (Equiv.refl (Fin 1)) .refl
  change Named.JointOpening ((scopedVoterElection ns swap left right extra ch).rename id)
    (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch .start)
      (Equiv.refl Nat) (Equiv.refl Nat))
  rw [Named.rename_id]
  have hid := Named.mappedState_identity ch.privateChannels
    (sourceState ns swap left right extra ch .start)
  exact (congrArg (Named.JointOpening (scopedVoterElection ns swap left right extra ch)) hid).mpr
    ((scopedVoterElection_normalizes ns hf swap left right hl hr extra ch).symm.jointOpening
      (sourceState ns swap left right extra ch .start))

/-- Arbitrary valid ground parameters admit one initial allocation for every
finite execution. Nonce/parameter freshness is proved by the allocator. -/
theorem exists_scoped_execution_phase (left right : CandidateSubstitution n Empty) :
    ∃ ns : Names n, ns.Fresh ∧ ∀ swap extra ch, ch.Fresh →
      ∀ {V : Type} {a : Named V}, Named.Execution (scopedVoterElection ns swap left right extra ch) a →
        ∃ (phase : Process.Phase) (e k : Nat ≃ Nat) (i : V ≃ Fin phase.handles),
          Process.Reachable ns swap left right extra phase ∧
          Named.JointOpening (a.rename i)
            (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k) := by
  obtain ⟨ns,hf,hl,hr,_⟩ := exists_parameter_fresh_election left.value right.value
  exact ⟨ns,hf,fun swap extra ch hc _ _ h =>
    scopedVoterElection_execution_phase ns hf swap left right hl hr extra ch hc h⟩

/-- No arbitrary raw state reached from the scoped election can output an old
handle, including after mixed actions, alpha detours and handle relabelling. -/
theorem scopedVoterElection_execution_no_handle_output (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (hl : NoncesFreshFor ns left.value)
    (hr : NoncesFreshFor ns right.value) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    {a : Named V} (h : Named.Execution (scopedVoterElection ns swap left right extra ch) a)
    (c : Nat) (x : V) (b : Named V) : ¬ Named.FreeStep a (.output c x) b := by
  obtain ⟨phase,e,k,i,ht,ha⟩ := scopedVoterElection_execution_phase ns hf swap left right hl hr extra ch hc h
  intro ho
  exact source_coordinated_no_handle_output ns hf swap left right extra ch e k phase ht ha
    c (i x) (b.rename i) (ho.rename_equiv i)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
