import ExplainableCrypto.Helios.Symbolic.SourceOpeningInternalInterpretation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {handles : Nat}

/-- An arbitrary actual source reduction from a structural representative of a
canonical state yields an actual Tau of a coherently fresh permutation of that
state. The raw target retains its full interpretation in the same fresh frame.
This includes both conditional outcomes and all original source contexts. -/
theorem Reduction.fresh_canonical_interpretation (s : ScopedState restricted handles)
    {a b : Named (Fin handles)} (hs : Structural (restrictedState hidden s) a)
    (h : Reduction a b) (avoid : Finset SourceName) :
    ∃ (ns : List SourceName) (c : Extended (Fin handles)) (e k : Nat ≃ Nat) (q : Agent Empty),
      Opens (restrictedState hidden s) NameAssignment.literal ns c ∧ ns.Nodup ∧
      (∀ n ∈ ns, n ∉ avoid) ∧
      Structural (restrictedState hidden s) (Named.restrictNames ns (.embed c)) ∧
      c = Extended.frameProcess (s.frame.mapNames e) (s.body.mapNames e k) ∧
      Agent.Tau (s.body.mapNames e k) q ∧
      b.Interprets NameAssignment.literal (s.frame.mapNames e).value q := by
  have hr : Reduction (restrictedState hidden s) b := .congr hs h (.refl _)
  obtain ⟨needed,hh⟩ := hr.opening_interpretation
  obtain ⟨ns,c,e,k,ho,hn,hf,hc,he,hp,_⟩ := exists_fresh_canonical_opening s (avoid ∪ needed)
  obtain ⟨q,hq,hb⟩ := hh ns c ho
    (fun n hn hm => hf n hn (Finset.mem_union_right _ hm)) _ _ hp
  exact ⟨ns,c,e,k,q,ho,hn,fun n hn hm => hf n hn (Finset.mem_union_left _ hm),hc,he,hq,hb⟩

/-- Return the actual Tau to the original canonical coordinates while keeping
the raw target's environment and full continuation coherently permuted. -/
theorem Reduction.canonical_tau (s : ScopedState restricted handles)
    {a b : Named (Fin handles)} (hs : Structural (restrictedState hidden s) a)
    (h : Reduction a b) :
    ∃ (e k : Nat ≃ Nat) (q : Agent Empty), Agent.Tau s.body q ∧
      b.Interprets NameAssignment.literal (s.frame.mapNames e).value (q.mapNames e k) := by
  obtain ⟨_,_,e,k,q,_,_,_,_,_,hq,hb⟩ := h.fresh_canonical_interpretation s hs ∅
  refine ⟨e,k,q.mapNames e.symm k.symm,?_,?_⟩
  · simpa only [Agent.mapNames_inverse] using hq.mapNames e.symm k.symm
  · simpa only [show (q.mapNames e.symm k.symm).mapNames e k = q from
      Agent.mapNames_inverse q e.symm k.symm] using hb

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
