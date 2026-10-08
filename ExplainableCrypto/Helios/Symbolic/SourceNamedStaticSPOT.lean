import ExplainableCrypto.Helios.Symbolic.SourceNamedElectionStatic
import ExplainableCrypto.Helios.Symbolic.SourceNamedAdmissibilitySPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceNamedStaticSPOT
open Historical General Source Extended

abbrev p := SourceNamedAdmissibilitySPOT.beforeState
abbrev stop : ScopedState {40} 1 := ⟨SourceAtomicOutputSPOT.oldFrame,.nil⟩

/-- A complete actual private-key frame supplies its own source presentation. -/
theorem actual_restricted_frame_reflexive :
    Named.StaticEq (Named.restrictedState ∅ p) (Named.restrictedState ∅ p) :=
  (Named.restrictedState_represents p).staticEq_self

theorem missing_domain_cannot_have_static_witness (b : Named (Fin 1)) :
    ¬ Named.StaticEq (.embed (.plain .nil)) b := fun h => h.complete_domains.1 0

theorem duplicate_frame_cannot_have_static_witness (b : Named (Fin 1)) :
    ¬ Named.StaticEq (.par (.embed (.active 0 (.name 40))) (.embed (.active 0 (.name 40)))) b := by
  intro h
  exact h.wellFormed.1.1.2.2 0 ⟨rfl,rfl⟩

/-- The required observation certificate rejects zero versus one for every
common private-name policy. This is a certificate-level separation control. -/
theorem changed_public_value_certificate_rejected (restricted : Finset Nat) :
    ¬ (⟨fun _ => .const .zero⟩ : Frame restricted 1).StaticEq ⟨fun _ => .const .one⟩ := by
  intro h
  have he := (h (.var 0) (.const .zero) True.intro True.intro).mp (EqE.refl _)
  exact zero_not_one he.symm

private theorem publication : Named.BoundOutput (Named.restrictedState ∅ p) 0
    (Named.restrictedCapture ∅ p.frame SourceVisibleInterpretationSPOT.proofPayload .nil) :=
  (Named.BoundOutput.embed (frame_output_derivable _ _ _ _)).restrictNames _
    ((Named.output_restriction_fresh_iff 0).mpr (by simp))

/-- Equal current frames do not prove behavior matching: one body outputs a
complete proof and the stopped body cannot perform any such bound output. -/
theorem static_clause_does_not_supply_dynamic_matching :
    Named.StaticEq (Named.restrictedState ∅ p) (Named.restrictedState ∅ stop) ∧
    Named.BoundOutput (Named.restrictedState ∅ p) 0
      (Named.restrictedCapture ∅ p.frame SourceVisibleInterpretationSPOT.proofPayload .nil) ∧
    ∀ b, ¬ Named.BoundOutput (Named.restrictedState ∅ stop) 0 b := by
  refine ⟨Named.restrictedState_staticEq_of_frames p stop (.refl _),publication,?_⟩
  intro b h
  simpa only [stop,Agent.channels,Finset.notMem_empty] using
    ((Named.channel_mem_restrictedState ∅ stop 0).mp h.channel_mem).1

theorem actual_output_reclosure_keeps_presented_frame :
    (Named.newVar (Named.restrictedCapture ∅ p.frame SourceVisibleInterpretationSPOT.proofPayload .nil)).RepresentsFrame
      ∅ p.frame := (Named.restrictedState_represents p).bound_reclose publication

theorem completed_zero_extra_named_staticEq :
    Named.StaticEq
      (Named.restrictedState Channels.canonical.privateChannels
        (sourceState SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right 0 Channels.canonical (.done [])))
      (Named.restrictedState Channels.canonical.privateChannels
        (sourceState SharedTallySPOT.names true SharedTallySPOT.left SharedTallySPOT.right 0 Channels.canonical (.done []))) :=
  Named.reachable_source_staticEq NumericReflectionSPOT.fixture_names_fresh
    (HistoricalProcessSPOT.zero_extra_completes false) Channels.canonical

theorem completed_two_extra_named_staticEq :
    Named.StaticEq
      (Named.restrictedState Channels.canonical.privateChannels
        (sourceState SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right 2 Channels.canonical
          (.done [SharedTallySPOT.first,SharedTallySPOT.second])))
      (Named.restrictedState Channels.canonical.privateChannels
        (sourceState SharedTallySPOT.names true SharedTallySPOT.left SharedTallySPOT.right 2 Channels.canonical
          (.done [SharedTallySPOT.first,SharedTallySPOT.second]))) :=
  Named.reachable_source_staticEq NumericReflectionSPOT.fixture_names_fresh
    (HistoricalProcessSPOT.two_extra_complete false) Channels.canonical

theorem rejected_named_staticEq :
    Named.StaticEq
      (Named.restrictedState Channels.canonical.privateChannels
        (sourceState SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical (.rejected [])))
      (Named.restrictedState Channels.canonical.privateChannels
        (sourceState SharedTallySPOT.names true SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical (.rejected []))) :=
  Named.reachable_source_staticEq NumericReflectionSPOT.fixture_names_fresh
    (HistoricalProcessSPOT.replay_stops false).1 Channels.canonical

abbrev fullTest : Recipe 1 := .spk (.var 0) (.name 41) (.const .zero)
  (.ternary .penc (.var 0) (.name 48) (.name 40))

/-- Even the old private literal in the fourth field is kept as the exact
query literal; the common presentations are freshly alpha-renamed around it. -/
theorem unchanged_full_recipe_test_witness :
    ∃ (hidden restricted : Finset Nat) (φ ψ : Frame restricted 1),
      (Named.restrictedState ∅ p).RepresentsFrame hidden φ ∧
      (Named.restrictedState ∅ p).RepresentsFrame hidden ψ ∧
      fullTest.Public restricted ∧ (Term.var (0 : Fin 1)).Public restricted ∧ φ.StaticEq ψ ∧
      (EqE (φ.eval fullTest) (φ.eval (.var 0)) ↔ EqE (ψ.eval fullTest) (ψ.eval (.var 0))) :=
  actual_restricted_frame_reflexive.test_witness fullTest (.var 0)

theorem common_witness_avoids_test_names :
    ∃ (hidden restricted : Finset Nat) (φ ψ : Frame restricted 1),
      (Named.restrictedState ∅ p).RepresentsFrame hidden φ ∧
      (Named.restrictedState ∅ p).RepresentsFrame hidden ψ ∧ φ.StaticEq ψ ∧
      ∀ n ∈ Named.restrictionNames hidden restricted,
        n ∉ ({.base 40,.base 41,.base 48,.channel 0} : Finset SourceName) :=
  actual_restricted_frame_reflexive.fresh_witness _

abbrev handshakeBefore : ScopedState {40} 1 := ⟨SourceAtomicOutputSPOT.oldFrame,
  .par SourceOperationalPrenexSPOT.sender SourceOperationalPrenexSPOT.receiver⟩
abbrev handshakeAfter : ScopedState {40} 1 := ⟨SourceAtomicOutputSPOT.oldFrame,SourceOperationalPrenexSPOT.afterComm⟩

/-- A real private communication retains the same static witness after a
nonempty silent path, with both the key and channel restrictions present. -/
theorem private_communication_static_witness :
    Named.StaticEq (Named.restrictedState {8} handshakeAfter) (Named.restrictedState {8} handshakeBefore) := by
  have hr : Named.Reduction (Named.restrictedState {8} handshakeBefore) (Named.restrictedState {8} handshakeAfter) := by
    apply Named.Reduction.restrictNames
    apply Named.Reduction.embed
    apply Extended.Reduction.parRight
    exact tau_ground_derivable _ (Agent.Tau.of_core (.comm _ _ _ _))
  exact (Named.restrictedState_represents handshakeBefore).staticEq_self.internal_star_left
    (Relation.ReflTransGen.single hr)

end ExplainableCrypto.Helios.Symbolic.SourceNamedStaticSPOT
