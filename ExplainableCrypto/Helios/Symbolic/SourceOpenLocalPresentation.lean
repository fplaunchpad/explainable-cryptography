import ExplainableCrypto.Helios.Symbolic.SourceRawCommunicationMatching

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {handles : Nat}

/-- Open one existing local in a presented frame. An auxiliary original output
of that local derives the required extra public value through the completed
output bridge; it supplies no new semantic or structural assumption. -/
theorem BinderStructural.open_local_frame {a : Extended (Option (Fin handles))}
    {φ : Frame ∅ handles} (h : (Extended.newVar a).frameOf.BinderStructural (activeFrame φ)) :
    ∃ ψ : Frame ∅ (handles+1),
      (a.frameOf.rename outputHandle).BinderStructural (activeFrame ψ) := by
  let probe : Extended (Fin handles) := .newVar (.par a (.plain (.output 0 (.var none) .nil)))
  let target : Extended (Option (Fin handles)) := .par a (.plain .nil)
  have hout : Named.BoundOutput (.embed probe) 0 (.embed target) :=
    .embed (.openAtom (.parRight a (.output 0 none .nil)))
  have hp : (Named.embed probe).RepresentsFrame ∅ φ := by
    have hs : probe.frameOf.BinderStructural (activeFrame φ) :=
      (Structural.newVar (Structural.zero a.frameOf)).binderStructural.trans h
    simpa only [Named.RepresentsFrame,Named.frameOf,Named.canonicalFrame,Named.restrictionNames,
      Finset.toList_empty,List.map_nil,List.append_nil,Named.restrictNames,List.foldr_nil] using hs.named
  have hopen : Named.Opens (.embed target) NameAssignment.literal [] target := by
    simpa only [show NameAssignment.literal.base = id from rfl,
      show NameAssignment.literal.channel = id from rfl,mapNames_id] using
      Named.Opens.embed target NameAssignment.literal
  obtain ⟨f,m,ht⟩ := hout.opened_frame_presentation hp hopen
  refine ⟨((φ.mapNames f).extend m).withPolicy ∅,?_⟩
  have hz := (Structural.zero a.frameOf).rename outputHandle outputHandle.injective
  exact hz.symm.binderStructural.trans ht

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
