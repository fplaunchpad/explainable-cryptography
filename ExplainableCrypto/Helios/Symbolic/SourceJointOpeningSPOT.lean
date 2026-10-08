import ExplainableCrypto.Helios.Symbolic.SourceJointOpeningPolicy
import ExplainableCrypto.Helios.Symbolic.SourceVisibleInvariantSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceJointOpeningSPOT
open Historical General Source SourceVisibleInvariantSPOT

theorem canonical_joint_opening :
    Named.JointOpening (Named.restrictedState {8} canonical) (Named.restrictedState {8} canonical) :=
  Named.restrictedState_jointOpening canonical

theorem public_joint_opening : Named.JointOpening rawPublic rawPublic :=
  Named.JointOpening.embed (.refl _) (Extended.frameProcess_realizes φ outputCode)

theorem private_public_pair_rejected :
    ¬ Named.JointOpening rawPublic (Named.restrictedState {8} canonical) := by
  intro h
  exact h.bound_channel_public canonical unrestricted_process_exposes_channel (by decide)

theorem public_private_pair_rejected :
    ¬ Named.JointOpening (Named.restrictedState {8} canonical) rawPublic :=
  fun h => private_public_pair_rejected h.symm

theorem old_body_invariant_is_strictly_weaker :
    Named.HasCanonicalOpening rawPublic φ outputCode ∧
    ¬ Named.JointOpening rawPublic (Named.restrictedState {8} canonical) :=
  ⟨unrestricted_process_has_body_invariant,private_public_pair_rejected⟩

abbrev alphaBody : Named (Fin 1) := .embed (Extended.frameProcess φ outputCode)
abbrev alphaBefore : Named (Fin 1) := .newName (.channel 8) alphaBody
noncomputable abbrev alphaAfter : Named (Fin 1) :=
  .newName (.channel 18) (alphaBody.mapNames id (Equiv.swap 8 18))

theorem alpha_before_realizes :
    Named.Opens alphaBefore NameAssignment.literal [.channel 18]
      ((Extended.frameProcess φ outputCode).mapNames id (Equiv.swap 8 18)) := by
  apply Named.Opens.newName (.channel 8) 18 _ (by simp)
  convert Named.Opens.embed (Extended.frameProcess φ outputCode)
    (Function.update NameAssignment.literal (.channel 8) 18) using 1
  exact (Extended.frameProcess φ outputCode).mapAssignments_congr
    (NameAssignment.permutations (Equiv.refl Nat) (Equiv.swap 8 18))
    (Function.update NameAssignment.literal (.channel 8) 18) (by decide)

theorem alpha_before_joint : Named.JointOpening alphaBefore alphaBefore := by
  refine ⟨[.channel 18],_,[.channel 18],_,alpha_before_realizes,alpha_before_realizes,
    ?_,?_,.refl _,_,_,(Extended.frameProcess_realizes φ outputCode).mapNames id (Equiv.swap 8 18)⟩ <;> decide

theorem actual_alpha_preserves_joint : Named.JointOpening alphaBefore alphaAfter :=
  alpha_before_joint.structural_right (Named.Structural.alphaChannel alphaBody 8 18 (by decide))

theorem alpha_private_output_stays_blocked (b : Named (Option (Fin 1))) :
    ¬ Named.BoundOutput alphaAfter 8 b := by
  intro h
  have hc := h.channel_mem
  rw [← actual_alpha_preserves_joint.channels] at hc
  change 8 ∈ (Extended.frameProcess φ outputCode).channels.erase 8 at hc
  exact (Finset.mem_erase.mp hc).1 rfl

theorem unused_restriction_preserves_joint :
    Named.JointOpening rawPublic (.newName (.channel 18) rawPublic) := by
  apply public_joint_opening.structural_right
  exact (Named.Structural.restrictNames_unused [.channel 18] rawPublic (by decide)).symm

theorem refresh_avoids_both_old_spellings :
    ∃ ns b ms c,
      Named.Opens alphaBefore NameAssignment.literal ns b ∧
      Named.Opens alphaAfter NameAssignment.literal ms c ∧
      (∀ n ∈ ns, n ∉ ({.channel 8,.channel 18} : Finset SourceName)) ∧
      (∀ n ∈ ms, n ∉ ({.channel 8,.channel 18} : Finset SourceName)) ∧
      b.SameRealizations c ∧ ∃ env p, b.Realizes env p := by
  obtain ⟨ns,b,ms,c,ha,hd,hf,hg,he,hr⟩ := actual_alpha_preserves_joint.fresh {.channel 8,.channel 18}
  exact ⟨ns,b,ms,c,ha,hd,fun n hn hh => hf n hn (Finset.mem_union_left _ hh),
    fun n hn hh => hg n hn (Finset.mem_union_left _ hh),he,hr⟩

abbrev inconsistent : Extended (Fin 1) := .par (.active 0 (.name 40)) (.active 0 (.name 41))
abbrev inconsistentOutput : Extended (Fin 1) := .par inconsistent (.plain (Extended.groundAgent outputCode))

theorem inconsistent_has_no_realization (env : Fin 1 → Ground) (p : Agent Empty) :
    ¬ inconsistent.Realizes env p := by
  rintro ⟨q,r,ha,hb,_⟩
  have he := (EqE.name_iff 40 41).mp (ha.1.symm.trans hb.1)
  cases he

theorem inconsistent_output_has_no_realization (env : Fin 1 → Ground) (p : Agent Empty) :
    ¬ inconsistentOutput.Realizes env p := by
  rintro ⟨q,r,ha,_,_⟩
  exact inconsistent_has_no_realization env q ha

theorem empty_classes_can_hide_different_channels :
    inconsistent.SameRealizations inconsistentOutput ∧ inconsistent.channels ≠ inconsistentOutput.channels := by
  refine ⟨fun env p => iff_of_false (inconsistent_has_no_realization env p)
    (inconsistent_output_has_no_realization env p),?_⟩
  decide

theorem nonvacuity_rejects_inconsistent_self :
    ¬ Named.JointOpening (.embed inconsistent) (.embed inconsistent) := by
  rintro ⟨ns,b,ms,c,ha,_,_,_,_,env,p,hr⟩
  cases ha
  exact inconsistent_has_no_realization env p hr

theorem complete_continuation_channels_are_retained : outputCode.channels = {8,9,10} := by decide

end ExplainableCrypto.Helios.Symbolic.SourceJointOpeningSPOT
