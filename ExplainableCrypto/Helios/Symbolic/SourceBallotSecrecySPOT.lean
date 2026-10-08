import ExplainableCrypto.Helios.Symbolic.SourceBallotSecrecy
import ExplainableCrypto.Helios.Symbolic.SourceElectionRelationSPOT
import ExplainableCrypto.Helios.Symbolic.SourceNamedStaticSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceBallotSecrecySPOT
open Historical General Source SourceReachableElectionSPOT

/-- The final theorem is instantiated at arbitrary finite administration size,
with the literal independent candidate/name fixture and actual voter scopes. -/
theorem arbitrary_administration_secrecy (extra : Nat) :
    Named.WeakLabelledBisimilar (scopedVoterElection ns false left right extra ch)
      (scopedVoterElection ns true left right extra ch) :=
  scopedVoterElection_ballot_secrecy ns NumericReflectionSPOT.fixture_names_fresh left right
    (by unfold NoncesFreshFor; decide) (by unfold NoncesFreshFor; decide) extra ch Channels.canonical_fresh

theorem actual_scoped_reverse_direction (extra : Nat) :
    Named.WeakLabelledBisimilar (scopedVoterElection ns true left right extra ch)
      (scopedVoterElection ns false left right extra ch) := (arbitrary_administration_secrecy extra).symm

/-- A retained actual input and rejection continue to be related by the final
weak source relation, with the exact component-replay input label. -/
theorem actual_replay_rejection_is_weakly_matched (swap swap' : Bool) :
    ∃ b d, Named.FreeStep (raw swap' (.input [])) (.input 4 (.var (1 : Fin 3))) b ∧
      Named.Reduction b d ∧ Named.WeakLabelledBisimilar (raw swap (.rejected [])) d := by
  obtain ⟨b,d,hb,hd,hr,_⟩ := SourceElectionRelationSPOT.replay_input_then_rejection_preserves_one_relation swap swap'
  exact ⟨b,d,hb,hd,SourceElectionRelation initial ns left right 1 ch,
    source_reachable_weak_bisimulation initial ns NumericReflectionSPOT.fixture_names_fresh
      left right 1 ch Channels.canonical_fresh,hr⟩

/-- Equal current frames with an output-capable and a stopped body fail the
final weak-bisimilarity definition. Silent steps cannot manufacture a channel. -/
theorem static_equivalence_does_not_prove_weak_bisimilarity :
    Named.StaticEq (Named.restrictedState ∅ SourceNamedStaticSPOT.p)
      (Named.restrictedState ∅ SourceNamedStaticSPOT.stop) ∧
    ¬ Named.WeakLabelledBisimilar (Named.restrictedState ∅ SourceNamedStaticSPOT.p)
      (Named.restrictedState ∅ SourceNamedStaticSPOT.stop) := by
  obtain ⟨he,ho,_⟩ := SourceNamedStaticSPOT.static_clause_does_not_supply_dynamic_matching
  refine ⟨he,?_⟩
  rintro ⟨R,hr,hab⟩
  obtain ⟨b,⟨a',b',ht,ho',_⟩,_⟩ := hr.bound hab ho
  have hm := Named.reduction_star_channels_subset ht ho'.channel_mem
  have hc := ((Named.channel_mem_restrictedState ∅ SourceNamedStaticSPOT.stop 0).mp hm).1
  simp only [Agent.channels,Finset.notMem_empty] at hc

/-- Omitting the complete exported domain cannot make the theorem vacuous. -/
theorem missing_domain_is_not_weakly_bisimilar (a : Named (Fin 1)) :
    ¬ Named.WeakLabelledBisimilar (.embed (.plain .nil)) a := by
  intro h
  exact h.staticEq.complete_domains.1 0

end ExplainableCrypto.Helios.Symbolic.SourceBallotSecrecySPOT
