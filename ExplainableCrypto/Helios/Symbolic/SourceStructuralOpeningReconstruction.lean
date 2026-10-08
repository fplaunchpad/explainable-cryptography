import ExplainableCrypto.Helios.Symbolic.SourceStructuralActionOpenings
import ExplainableCrypto.Helios.Symbolic.SourceNamePrefixPolicies

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- Reclosing the allocated prefix introduces no new free source names. -/
theorem Opens.reclosed_freeNames_subset {a : Named V} {ns : List SourceName}
    {b : Extended V} (h : Opens a NameAssignment.literal ns b) :
    (restrictNames ns (.embed b)).freeNames ⊆ a.freeNames := by
  intro n hn
  rw [freeNames_restrictNames] at hn
  obtain ⟨hb,hns⟩ := Finset.mem_sdiff.mp hn
  have hs := h.nameSupport hb
  have hid : SourceName.map NameAssignment.literal.base NameAssignment.literal.channel = id := by
    funext n; cases n <;> rfl
  simp only [hid,Finset.image_id] at hs
  exact (Finset.mem_union.mp hs).resolve_right hns

/-- Jointly fresh literal openings with actual binder-structural bodies
reconstruct an original Named structural path. Allocation lists may differ. -/
theorem Opens.structural_of_binder {a d : Named V} {ns ms : List SourceName}
    {b c : Extended V} (ha : Opens a NameAssignment.literal ns b)
    (hd : Opens d NameAssignment.literal ms c)
    (hn : ∀ n ∈ ns, n ∉ a.allNames ∪ d.allNames)
    (hm : ∀ n ∈ ms, n ∉ a.allNames ∪ d.allNames)
    (h : b.BinderStructural c) : Structural a d := by
  have hs := ha.structural_literal (fun n hns hmem => hn n hns (Finset.mem_union_left _ hmem))
  have ht := hd.structural_literal (fun n hms hmem => hm n hms (Finset.mem_union_right _ hmem))
  have hpadA := Structural.restrictNames_unused ms (restrictNames ns (.embed b))
    (fun n hms hmem => hm n hms (Finset.mem_union_left _
      (freeNames_subset_allNames a (ha.reclosed_freeNames_subset hmem))))
  have hpadD := Structural.restrictNames_unused ns (restrictNames ms (.embed c))
    (fun n hns hmem => hn n hns (Finset.mem_union_right _
      (freeNames_subset_allNames d (hd.reclosed_freeNames_subset hmem))))
  have horder : (ms ++ ns).toFinset = (ns ++ ms).toFinset := by
    simp only [List.toFinset_append,Finset.union_comm]
  have hbody := (h.named.restrictNames (ms ++ ns)).trans
    (Structural.restrictNames_of_toFinset_eq (ms ++ ns) (ns ++ ms) horder (.embed c))
  rw [restrictNames_append,restrictNames_append] at hbody
  exact hs.trans (hpadA.symm.trans (hbody.trans (hpadD.trans ht.symm)))

/-- Structural equivalence supplies paired binder-structural openings avoiding
any finite context and every literal name in either original process. -/
theorem Structural.fresh_binder_openings {a d : Named V} (h : Structural a d)
    (avoid : Finset SourceName) :
    ∃ ns b ms c,
      Opens a NameAssignment.literal ns b ∧ Opens d NameAssignment.literal ms c ∧
      (∀ n ∈ ns, n ∉ avoid ∪ (a.allNames ∪ d.allNames)) ∧
      (∀ n ∈ ms, n ∉ avoid ∪ (a.allNames ∪ d.allNames)) ∧ b.BinderStructural c := by
  obtain ⟨ns,b,hb,hf⟩ := exists_fresh_opening a NameAssignment.literal
    (avoid ∪ (a.allNames ∪ d.allNames))
  obtain ⟨ms,c,hc,hg,he⟩ := h.transport_binder_opening _ ns b
    (avoid ∪ (a.allNames ∪ d.allNames)) hb hf
  exact ⟨ns,b,ms,c,hb,hc,hf,hg,he⟩

/-- This characterizes actual structural equivalence, including unused
restrictions and variable exchange; mere equality of realizations is weaker. -/
theorem structural_iff_fresh_binder_openings (a d : Named V) :
    Structural a d ↔ ∃ ns b ms c,
      Opens a NameAssignment.literal ns b ∧ Opens d NameAssignment.literal ms c ∧
      (∀ n ∈ ns, n ∉ a.allNames ∪ d.allNames) ∧
      (∀ n ∈ ms, n ∉ a.allNames ∪ d.allNames) ∧ b.BinderStructural c := by
  constructor
  · intro h
    simpa only [Finset.empty_union] using h.fresh_binder_openings ∅
  · rintro ⟨ns,b,ms,c,ha,hd,hn,hm,h⟩
    exact ha.structural_of_binder hd hn hm h

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
