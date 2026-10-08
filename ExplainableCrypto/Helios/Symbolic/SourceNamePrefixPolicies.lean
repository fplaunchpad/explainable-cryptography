import ExplainableCrypto.Helios.Symbolic.SourceAdministrationNameSupport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- Repeated names in an adjacent restriction prefix contribute no additional
free-name binding. Remove them through actual unused-name rules. -/
theorem Structural.restrictNames_dedup (ns : List SourceName) (a : Named V) :
    Structural (Named.restrictNames ns a) (Named.restrictNames ns.dedup a) := by
  induction ns with
  | nil => exact .refl _
  | cons n ns ih =>
    by_cases hn : n ∈ ns
    · have hf : n ∉ (Named.restrictNames ns a).freeNames := by
        simp only [freeNames_restrictNames,Finset.mem_sdiff,List.mem_toFinset]
        exact fun h => h.2 hn
      simpa only [List.dedup_cons,if_pos hn,Named.restrictNames,List.foldr_cons] using
        (Structural.name_unused (Named.restrictNames ns a) n hf).trans ih
    · simpa only [List.dedup_cons,if_neg hn,Named.restrictNames,List.foldr_cons] using
        Structural.newName n ih

/-- Prefix order and duplicate presentation are immaterial when the exact
set of restricted source names is the same. This is not policy padding. -/
theorem Structural.restrictNames_of_toFinset_eq (ns ms : List SourceName)
    (he : ns.toFinset = ms.toFinset) (a : Named V) :
    Structural (Named.restrictNames ns a) (Named.restrictNames ms a) := by
  have hs : ns.dedup.toFinset = ms.dedup.toFinset := by
    ext n
    simpa only [List.mem_toFinset,List.mem_dedup] using Finset.ext_iff.mp he n
  have hp := List.perm_of_nodup_nodup_toFinset_eq (List.nodup_dedup ns) (List.nodup_dedup ms) hs
  exact (Structural.restrictNames_dedup ns a).trans
    ((Structural.restrictNames_perm _ _ hp a).trans (Structural.restrictNames_dedup ms a).symm)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
