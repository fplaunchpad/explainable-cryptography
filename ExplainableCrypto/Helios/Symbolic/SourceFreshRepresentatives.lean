import ExplainableCrypto.Helios.Symbolic.SourceBoundNames

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named

/-- Freshen all current name binders away from an arbitrary finite avoidance
set, using only the existing structural rules. Inner binders are first made
fresh for the old outer binder, so the subsequent alpha swap cannot move them. -/
theorem exists_fresh_boundNames (a : Named V) (avoid : Finset SourceName) :
    ∃ b : Named V, Structural a b ∧ ∀ n ∈ b.boundNames, n ∉ avoid := by
  induction a generalizing avoid with
  | embed a => exact ⟨.embed a,.refl _,by simp [boundNames]⟩
  | par a b ha hb =>
    obtain ⟨a',hs,hf⟩ := ha avoid
    obtain ⟨b',ht,hg⟩ := hb avoid
    refine ⟨.par a' b',(Structural.parLeft b hs).trans (Structural.parRight a' ht),?_⟩
    intro n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · exact hf n hn
    · exact hg n hn
  | newVar a ha =>
    obtain ⟨b,hs,hf⟩ := ha avoid
    exact ⟨.newVar b,.newVar hs,hf⟩
  | newName n a ha =>
    obtain ⟨b,hs,hf⟩ := ha (insert n avoid)
    have hn : n ∉ b.boundNames := fun h => hf n h (Finset.mem_insert_self _ _)
    have hold : ∀ u ∈ b.boundNames, u ∉ avoid :=
      fun u hu hmem => hf u hu (Finset.mem_insert_of_mem hmem)
    let m := freshNameIndex (b.allNames ∪ avoid)
    cases n with
    | base n =>
      have hmAll : SourceName.base m ∉ b.allNames ∪ avoid := fresh_base_not_mem _
      have hm : SourceName.base m ∉ b.allNames := fun h => hmAll (Finset.mem_union_left _ h)
      have hmAvoid : SourceName.base m ∉ avoid := fun h => hmAll (Finset.mem_union_right _ h)
      have hmBound : SourceName.base m ∉ b.boundNames := fun h => hm (boundNames_subset_allNames b h)
      refine ⟨.newName (.base m) (b.mapNames (Equiv.swap n m) id),
        (Structural.newName (.base n) hs).trans (.alphaBase b n m hm),?_⟩
      intro u hu
      rw [boundNames,boundNames_base_swap b n m hn hmBound] at hu
      rcases Finset.mem_insert.mp hu with he | hu
      · exact he ▸ hmAvoid
      · exact hold u hu
    | channel n =>
      have hmAll : SourceName.channel m ∉ b.allNames ∪ avoid := fresh_channel_not_mem _
      have hm : SourceName.channel m ∉ b.allNames := fun h => hmAll (Finset.mem_union_left _ h)
      have hmAvoid : SourceName.channel m ∉ avoid := fun h => hmAll (Finset.mem_union_right _ h)
      have hmBound : SourceName.channel m ∉ b.boundNames := fun h => hm (boundNames_subset_allNames b h)
      refine ⟨.newName (.channel m) (b.mapNames id (Equiv.swap n m)),
        (Structural.newName (.channel n) hs).trans (.alphaChannel b n m hm),?_⟩
      intro u hu
      rw [boundNames,boundNames_channel_swap b n m hn hmBound] at hu
      rcases Finset.mem_insert.mp hu with he | hu
      · exact he ▸ hmAvoid
      · exact hold u hu

/-- Freshening never changes the chosen input/output label. All names in that
label are included in the avoidance set, including every input proof field. -/
theorem exists_fresh_for_free_label (a : Named V) (l : Extended.FreeLabel V) :
    ∃ b : Named V, Structural a b ∧ ∀ n ∈ b.boundNames, n ∉ l.nameSupport :=
  exists_fresh_boundNames a l.nameSupport

/-- A known source action can be transferred to the fresh representative using
Struct with the exact same label and target. This is not the converse from a
fresh representative to the normalized wrapper. -/
theorem FreeStep.fresh_representative {a b : Named V} {l : Extended.FreeLabel V} (h : FreeStep a l b) :
    ∃ a' : Named V, Structural a a' ∧ (∀ n ∈ a'.boundNames, n ∉ l.nameSupport) ∧ FreeStep a' l b := by
  obtain ⟨a',hs,hf⟩ := exists_fresh_for_free_label a l
  exact ⟨a',hs,hf,.congr hs.symm h (.refl _)⟩

theorem BoundOutput.fresh_representative {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (avoid : Finset SourceName) :
    ∃ a' : Named V, Structural a a' ∧ (∀ n ∈ a'.boundNames, n ∉ insert (.channel c) avoid) ∧ BoundOutput a' c b := by
  obtain ⟨a',hs,hf⟩ := exists_fresh_boundNames a (insert (.channel c) avoid)
  exact ⟨a',hs,hf,.congr hs.symm h (.refl _)⟩
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
