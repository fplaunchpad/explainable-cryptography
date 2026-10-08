import ExplainableCrypto.Helios.Symbolic.SourceUnusedRestrictions
import ExplainableCrypto.Helios.Symbolic.SourceFramePolicies

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type} {restricted hidden : Finset Nat} {handles : Nat}

namespace Extended

theorem groundTerm_nameSupport (m : Ground) : (groundTerm m : Term V).nameSupport = m.nameSupport := by
  have he : (Empty.elim : Empty → Term V) = fun v => .var (Empty.elim v) := by
    funext v; exact v.elim
  simpa only [groundTerm,he] using Term.nameSupport_rename m (Empty.elim : Empty → V)

theorem frameEntries_name_fresh_iff (h : Nat) (vars : Fin h → V) (values : Fin h → Ground) (n : SourceName) :
    n ∉ (frameEntries h vars values).nameSupport ↔
      ∀ i, n ∉ (values i).nameSupport.image SourceName.base := by
  induction h with
  | zero => simp [frameEntries,nameSupport,Agent.nameSupport]
  | succ h ih =>
    simp only [frameEntries,nameSupport,groundTerm_nameSupport,Finset.mem_union,not_or,ih]
    constructor
    · rintro ⟨hl,ht⟩ i
      exact Fin.lastCases hl (fun j => ht j) i
    · intro hf
      exact ⟨hf (Fin.last h),fun i => hf i.castSucc⟩

theorem activeFrame_base_fresh_iff (φ : Frame restricted handles) (n : Nat) :
    SourceName.base n ∉ (activeFrame φ).nameSupport ↔ n ∉ φ.nameSupport := by
  rw [activeFrame,frameEntries_name_fresh_iff]
  simp [Frame.mem_nameSupport]

theorem activeFrame_channel_fresh (φ : Frame restricted handles) (n : Nat) :
    SourceName.channel n ∉ (activeFrame φ).nameSupport := by
  rw [activeFrame,frameEntries_name_fresh_iff]
  simp
end Extended

namespace Named

/-- Pure extracted frames have no channel occurrences, so their channel-policy
wrappers can be changed freely. This does not apply to executable bodies. -/
theorem canonicalFrame_hidden_irrelevant (φ : Frame restricted handles) (hidden hidden' : Finset Nat) :
    Structural (canonicalFrame hidden φ) (canonicalFrame hidden' φ) := by
  have hc (hs : Finset Nat) : Structural (canonicalFrame hs φ)
      (Named.restrictNames (restricted.toList.map SourceName.base) (.embed (Extended.activeFrame φ))) := by
    rw [canonicalFrame,restrictionNames,restrictNames_append]
    apply (Structural.restrictNames_unused (hs.toList.map SourceName.channel) (.embed (Extended.activeFrame φ)) ?_).restrictNames
    intro n hn
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hn
    exact Extended.activeFrame_channel_fresh φ c
  exact (hc hidden).trans (hc hidden').symm

/-- Canonical prefix reordering exposes one added base restriction. -/
theorem canonicalFrame_insert_base (φ : Frame restricted handles) (hidden : Finset Nat) (n : Nat)
    (hn : n ∉ restricted) :
    Structural (canonicalFrame hidden (φ.withPolicy (insert n restricted)))
      (.newName (.base n) (canonicalFrame hidden φ)) := by
  have hp : (SourceName.base n :: restrictionNames hidden restricted).Perm
      (restrictionNames hidden (insert n restricted)) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.nodup_cons.mpr ⟨by simpa only [base_mem_restrictionNames] using hn,restrictionNames_nodup _ _⟩
    · exact restrictionNames_nodup _ _
    · ext u
      cases u <;> simp [base_mem_restrictionNames,channel_mem_restrictionNames]
  exact (Structural.restrictNames_perm _ _ hp (.embed (Extended.activeFrame φ))).symm

theorem canonicalFrame_base_padding (φ : Frame restricted handles) (hidden : Finset Nat) (extra : Finset Nat)
    (hf : ∀ n ∈ extra, n ∉ restricted → n ∉ φ.nameSupport) :
    Structural (canonicalFrame hidden (φ.withPolicy (restricted ∪ extra))) (canonicalFrame hidden φ) := by
  classical
  induction extra using Finset.induction_on with
  | empty =>
    simpa only [canonicalFrame,Frame.withPolicy,Extended.activeFrame,Finset.union_empty] using Structural.refl (canonicalFrame hidden φ)
  | @insert n extra hn ih =>
    have hi := ih (fun u hu => hf u (Finset.mem_insert_of_mem hu))
    by_cases hnr : n ∈ restricted ∪ extra
    · simpa only [canonicalFrame,Frame.withPolicy,Extended.activeFrame,Finset.union_insert,Finset.insert_eq_of_mem hnr] using hi
    · have hf' : n ∉ φ.nameSupport := hf n (Finset.mem_insert_self _ _)
        (fun h => hnr (Finset.mem_union_left _ h))
      have hfree : SourceName.base n ∉ (canonicalFrame hidden (φ.withPolicy (restricted ∪ extra))).freeNames := by
        rw [canonicalFrame,freeNames_restrictNames]
        intro h
        exact (Extended.activeFrame_base_fresh_iff _ n).mpr hf' (Finset.mem_sdiff.mp h).1
      have hs := (canonicalFrame_insert_base (φ.withPolicy (restricted ∪ extra)) hidden n hnr).trans
        (Structural.name_unused _ (.base n) hfree)
      simpa only [canonicalFrame,Frame.withPolicy,Extended.activeFrame,Finset.union_insert] using hs.trans hi

/-- Add only unused new base restrictions and choose any hidden channel
policy for this pure frame, retaining an actual canonical structural path. -/
theorem canonicalFrame_policy_padding (φ : Frame restricted handles) (hidden hidden' extra : Finset Nat)
    (hf : ∀ n ∈ extra, n ∉ restricted → n ∉ φ.nameSupport) :
    Structural (canonicalFrame hidden (φ.withPolicy (restricted ∪ extra))) (canonicalFrame hidden' φ) :=
  (canonicalFrame_base_padding φ hidden extra hf).trans (canonicalFrame_hidden_irrelevant φ hidden hidden')

theorem RepresentsFrame.pad_policy {a : Named (Fin handles)} {φ : Frame restricted handles}
    (h : a.RepresentsFrame hidden φ) (hidden' extra : Finset Nat)
    (hf : ∀ n ∈ extra, n ∉ restricted → n ∉ φ.nameSupport) :
    a.RepresentsFrame hidden' (φ.withPolicy (restricted ∪ extra)) :=
  h.trans (canonicalFrame_policy_padding φ hidden' hidden extra hf).symm

end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
