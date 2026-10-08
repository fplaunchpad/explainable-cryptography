import ExplainableCrypto.Helios.Symbolic.SourceVisibleReadiness

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {handles : Nat}

/-- A ready public input in the full joint realization supplies an actual raw
input with the unchanged recipe. Freshening is derived against all recipe names.
Matching its evaluated successor additionally uses the public-recipe condition
in the existing public_input_target theorem. -/
theorem JointOpening.input_available {a : Named (Fin handles)}
    {φ : Frame restricted handles} {p : Agent Empty}
    (ha : JointOpening a (restrictedState hidden ⟨φ,p⟩))
    {c : Nat} (hc : c ∉ hidden) (hp : p.HasInput c) (r : Recipe handles) :
    ∃ b, FreeStep a (.input c r) b := by
  let label := Extended.FreeLabel.input c r
  let F := Extended.frameProcess φ p
  obtain ⟨ns,d,ms,t,ho,hcan,hf,_,he,_⟩ := ha.fresh (a.allNames ∪ label.nameSupport)
  obtain ⟨τ,ht,_,hfix⟩ := hcan.prefix_pair_assignment (restrictionNames hidden restricted) F F
    NameAssignment.literal
  have hchannel : τ.channel c = c := hfix (.channel c)
    (fun h => hc ((channel_mem_restrictionNames c hidden restricted).mp h))
  have hd : d.Realizes (φ.mapNames τ.base).value (p.mapNames τ.base τ.channel) := by
    apply (he _ _).mpr
    rw [ht,Extended.frameProcess_mapNames]
    exact Extended.frameProcess_realizes _ _
  have hready : (p.mapNames τ.base τ.channel).HasInput c := by
    simpa only [hchannel] using hp.mapNames τ.base τ.channel
  obtain ⟨b,hb⟩ := Extended.input_available_of_realizes hd hready r
  have hs := ho.structural_literal (fun n hn hm => hf n hn
    (Finset.mem_union_left _ (Finset.mem_union_left _ hm)))
  have hstep := (FreeStep.embed hb).restrictNames ns
    (fun n hn hm => hf n hn (Finset.mem_union_left _ (Finset.mem_union_right _ hm)))
  exact ⟨_,.congr hs hstep (.refl _)⟩

/-- A ready public output has a real raw bound-output action. The derived source
rule retains the full term and all private restrictions; only the fresh variable
is exported. No target correspondence is assumed. -/
theorem JointOpening.bound_available {a : Named (Fin handles)}
    {φ : Frame restricted handles} {p : Agent Empty}
    (ha : JointOpening a (restrictedState hidden ⟨φ,p⟩))
    {c : Nat} (hc : c ∉ hidden) (hp : p.HasOutput c) :
    ∃ b, BoundOutput a c b := by
  let F := Extended.frameProcess φ p
  obtain ⟨ns,d,ms,t,ho,hcan,hf,_,he,_⟩ := ha.fresh (a.allNames ∪ {SourceName.channel c})
  obtain ⟨τ,ht,_,hfix⟩ := hcan.prefix_pair_assignment (restrictionNames hidden restricted) F F
    NameAssignment.literal
  have hchannel : τ.channel c = c := hfix (.channel c)
    (fun h => hc ((channel_mem_restrictionNames c hidden restricted).mp h))
  have hd : d.Realizes (φ.mapNames τ.base).value (p.mapNames τ.base τ.channel) := by
    apply (he _ _).mpr
    rw [ht,Extended.frameProcess_mapNames]
    exact Extended.frameProcess_realizes _ _
  have hready : (p.mapNames τ.base τ.channel).HasOutput c := by
    simpa only [hchannel] using hp.mapNames τ.base τ.channel
  obtain ⟨b,hb⟩ := Extended.bound_available_of_realizes hd hready
  have hs := ho.structural_literal (fun n hn hm => hf n hn
    (Finset.mem_union_left _ (Finset.mem_union_left _ hm)))
  have hstep := (BoundOutput.embed hb).restrictNames ns (by
    intro n hn hnc
    apply hf n hn
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [hnc])))
  exact ⟨_,.congr hs hstep (.refl _)⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
