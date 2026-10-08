import ExplainableCrypto.Helios.Symbolic.SourceFreshPrefixTools

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named

/-- Two processes under the same finite name prefix can choose one fresh
prefix and the same base/channel permutations. This retains coherent payload
renaming in both worlds rather than freshening them independently. -/
theorem exists_common_fresh_prefix (ns : List SourceName) (a : Named V) (b : Named W)
    (avoid : Finset SourceName) :
    ∃ (ns' : List SourceName) (e k : Nat ≃ Nat),
      Structural (restrictNames ns a) (restrictNames ns' (a.mapNames e k)) ∧
      Structural (restrictNames ns b) (restrictNames ns' (b.mapNames e k)) ∧
      (∀ u ∈ ns', u ∉ avoid) ∧ ns'.Nodup ∧ ns'.length = ns.length ∧
      (∀ u ∈ ns, u.map e k ∈ ns') ∧
      (∀ u ∈ avoid, u ∉ ns → u.map e k = u) := by
  induction ns generalizing avoid with
  | nil =>
    refine ⟨[],Equiv.refl Nat,Equiv.refl Nat,?_,?_,by simp,by simp,rfl,by simp,?_⟩
    · simpa only [restrictNames,List.foldr,Equiv.coe_refl,mapNames_id] using Structural.refl a
    · simpa only [restrictNames,List.foldr,Equiv.coe_refl,mapNames_id] using Structural.refl b
    · intro u _ _
      cases u <;> rfl
  | cons u ns ih =>
    obtain ⟨ns',e,k,ha,hb,hf,hnd,hlen,hi,hfix⟩ := ih (insert u avoid)
    let aa := restrictNames ns' (a.mapNames e k)
    let bb := restrictNames ns' (b.mapNames e k)
    let m := freshNameIndex (aa.allNames ∪ (bb.allNames ∪ avoid))
    have hu : u ∉ ns' := fun h => hf u h (Finset.mem_insert_self _ _)
    have hold : ∀ v ∈ ns', v ∉ avoid := fun v hv hm => hf v hv (Finset.mem_insert_of_mem hm)
    cases u with
    | base n =>
      have hmAll : SourceName.base m ∉ aa.allNames ∪ (bb.allNames ∪ avoid) := fresh_base_not_mem _
      have hma : SourceName.base m ∉ aa.allNames := fun h => hmAll (Finset.mem_union_left _ h)
      have hmb : SourceName.base m ∉ bb.allNames := fun h => hmAll (Finset.mem_union_right _ (Finset.mem_union_left _ h))
      have hmAvoid : SourceName.base m ∉ avoid := fun h => hmAll (Finset.mem_union_right _ (Finset.mem_union_right _ h))
      have hm : SourceName.base m ∉ ns' := fun h => hma (mem_allNames_of_mem_restriction ns' _ _ h)
      refine ⟨.base m :: ns',e.trans (Equiv.swap n m),k,?_,?_,?_,List.nodup_cons.mpr ⟨hm,hnd⟩,by simpa only [List.length_cons] using congrArg Nat.succ hlen,?_,?_⟩
      · apply (Structural.newName (.base n) ha).trans
        have hα := Structural.alphaBase aa n m hma
        change Structural (.newName (.base n) aa)
          (.newName (.base m) ((restrictNames ns' (a.mapNames e k)).mapNames (Equiv.swap n m) id)) at hα
        rw [mapNames_restrict_base_swap ns' _ n m hu hm] at hα
        simpa only [aa,restrictNames,List.foldr,mapNames_comp,Equiv.coe_trans,Function.comp_def,id] using hα
      · apply (Structural.newName (.base n) hb).trans
        have hα := Structural.alphaBase bb n m hmb
        change Structural (.newName (.base n) bb)
          (.newName (.base m) ((restrictNames ns' (b.mapNames e k)).mapNames (Equiv.swap n m) id)) at hα
        rw [mapNames_restrict_base_swap ns' _ n m hu hm] at hα
        simpa only [bb,restrictNames,List.foldr,mapNames_comp,Equiv.coe_trans,Function.comp_def,id] using hα
      · intro v hv
        rcases List.mem_cons.mp hv with he | hv
        · exact he ▸ hmAvoid
        · exact hold v hv
      · have hj := prefix_image_cons ns ns' (.base n) (.base m) (SourceName.map e k) (SourceName.map (Equiv.swap n m) id) hi
          (hfix (.base n) (Finset.mem_insert_self _ _))
          (fun w hw => SourceName.base_swap_fixes w n m (fun h => hu (h ▸ hw)) (fun h => hm (h ▸ hw)))
          (by simp [SourceName.map])
        simpa only [SourceName.map_comp,Equiv.coe_trans,Function.comp_def,id] using hj
      · have hj := prefix_fixes_avoid_cons ns (.base n) avoid (SourceName.map e k) (SourceName.map (Equiv.swap n m) id)
          (fun w hw => hfix w (Finset.mem_insert_of_mem hw))
          (fun w hw hn => SourceName.base_swap_fixes w n m hn (fun h => hmAvoid (h ▸ hw)))
        simpa only [SourceName.map_comp,Equiv.coe_trans,Function.comp_def,id] using hj
    | channel n =>
      have hmAll : SourceName.channel m ∉ aa.allNames ∪ (bb.allNames ∪ avoid) := fresh_channel_not_mem _
      have hma : SourceName.channel m ∉ aa.allNames := fun h => hmAll (Finset.mem_union_left _ h)
      have hmb : SourceName.channel m ∉ bb.allNames := fun h => hmAll (Finset.mem_union_right _ (Finset.mem_union_left _ h))
      have hmAvoid : SourceName.channel m ∉ avoid := fun h => hmAll (Finset.mem_union_right _ (Finset.mem_union_right _ h))
      have hm : SourceName.channel m ∉ ns' := fun h => hma (mem_allNames_of_mem_restriction ns' _ _ h)
      refine ⟨.channel m :: ns',e,k.trans (Equiv.swap n m),?_,?_,?_,List.nodup_cons.mpr ⟨hm,hnd⟩,by simpa only [List.length_cons] using congrArg Nat.succ hlen,?_,?_⟩
      · apply (Structural.newName (.channel n) ha).trans
        have hα := Structural.alphaChannel aa n m hma
        change Structural (.newName (.channel n) aa)
          (.newName (.channel m) ((restrictNames ns' (a.mapNames e k)).mapNames id (Equiv.swap n m))) at hα
        rw [mapNames_restrict_channel_swap ns' _ n m hu hm] at hα
        simpa only [aa,restrictNames,List.foldr,mapNames_comp,Equiv.coe_trans,Function.comp_def,id] using hα
      · apply (Structural.newName (.channel n) hb).trans
        have hα := Structural.alphaChannel bb n m hmb
        change Structural (.newName (.channel n) bb)
          (.newName (.channel m) ((restrictNames ns' (b.mapNames e k)).mapNames id (Equiv.swap n m))) at hα
        rw [mapNames_restrict_channel_swap ns' _ n m hu hm] at hα
        simpa only [bb,restrictNames,List.foldr,mapNames_comp,Equiv.coe_trans,Function.comp_def,id] using hα
      · intro v hv
        rcases List.mem_cons.mp hv with he | hv
        · exact he ▸ hmAvoid
        · exact hold v hv
      · have hj := prefix_image_cons ns ns' (.channel n) (.channel m) (SourceName.map e k) (SourceName.map id (Equiv.swap n m)) hi
          (hfix (.channel n) (Finset.mem_insert_self _ _))
          (fun w hw => SourceName.channel_swap_fixes w n m (fun h => hu (h ▸ hw)) (fun h => hm (h ▸ hw)))
          (by simp [SourceName.map])
        simpa only [SourceName.map_comp,Equiv.coe_trans,Function.comp_def,id] using hj
      · have hj := prefix_fixes_avoid_cons ns (.channel n) avoid (SourceName.map e k) (SourceName.map id (Equiv.swap n m))
          (fun w hw => hfix w (Finset.mem_insert_of_mem hw))
          (fun w hw hn => SourceName.channel_swap_fixes w n m hn (fun h => hmAvoid (h ▸ hw)))
        simpa only [SourceName.map_comp,Equiv.coe_trans,Function.comp_def,id] using hj
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
